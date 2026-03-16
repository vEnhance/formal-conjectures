/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.Util.Answer

section WithAuxiliary

open Google

open Lean Elab Meta

set_option google.answer "with_auxiliary"

open Lean Elab Meta

theorem foo : answer(True) := by
  run_tac Tactic.withMainContext do
    let env ← getEnv
    let some aux := env.find? `foo._answer | throwError "here"
  trivial

theorem bar : 1 = answer(sorry) := by
  run_tac Tactic.withMainContext do
    let env ← getEnv
    let some aux := env.find? `bar._answer | throwError "here"
  -- TODO(Paul-Lez): This will change when I write a delaborator
  guard_target = 1 = bar._answer
  sorry

theorem bar_symm : answer(sorry) = 1 := by
  run_tac Tactic.withMainContext do
    let env ← getEnv
    let some aux := env.find? `bar._answer | throwError "here"
  -- TODO(Paul-Lez): This will change when I write a delaborator
  guard_target = bar_symm._answer = 1
  sorry

theorem bar_symm_explicit : answer(1) = 1 := by
  run_tac Tactic.withMainContext do
    let env ← getEnv
    let some aux := env.find? `bar._answer | throwError "here"
  -- TODO(Paul-Lez): This will change when I write a delaborator
  guard_target = bar_symm_explicit._answer = 1
  sorry

theorem i_have_some_universes.{u, v} (X : Type u) (Y : Type v) : (X × Y) = answer(sorry) := by
  guard_target = (X × Y : Type (max u v)) = i_have_some_universes._answer.{u, v}
  sorry

-- Tests for answers that mention variables from the theorem's scope.

theorem answer_single_var (n : Nat) : n = answer(n) := by
  run_tac Tactic.withMainContext do
    let env ← getEnv
    let some _ := env.find? `answer_single_var._answer | throwError "auxiliary not found"
  guard_target = n = answer_single_var._answer n
  rfl

theorem answer_multi_var (n m : Nat) : n + m = answer(n + m) := by
  run_tac Tactic.withMainContext do
    let env ← getEnv
    let some _ := env.find? `answer_multi_var._answer | throwError "auxiliary not found"
  guard_target = n + m = answer_multi_var._answer n m
  rfl

-- Test that transitive dependencies are included: `v : Fin n` depends on `n`,
-- so even though `n` does not appear directly in `answer(v.val)`, it must be
-- a parameter of the auxiliary definition because it appears in `v`'s type.
theorem answer_dep_var (n : Nat) (v : Fin n) : v.val = answer(v.val) := by
  run_tac Tactic.withMainContext do
    let env ← getEnv
    let some _ := env.find? `answer_dep_var._answer | throwError "auxiliary not found"
  guard_target = v.val = answer_dep_var._answer n v
  rfl

-- Test with a type variable in the answer (both the type and the value are fvars,
-- so the auxiliary must be abstracted over both).
theorem answer_type_var (α : Type) (a : α) : a = answer(a) := by
  run_tac Tactic.withMainContext do
    let env ← getEnv
    let some _ := env.find? `answer_type_var._answer | throwError "auxiliary not found"
  guard_target = a = answer_type_var._answer α a
  rfl

-- Variable bound by ∀ in the type body (not a top-level theorem parameter).
-- When elaborating the body of `∀ (n : Nat), ...`, Lean introduces `n` as a
-- fvar just like a theorem parameter, so the auxiliary must still abstract it.
theorem answer_forall_bound : ∀ (n : Nat), n = answer(n) := by
  run_tac Tactic.withMainContext do
    let env ← getEnv
    let some _ := env.find? `answer_forall_bound._answer | throwError "auxiliary not found"
  intro n
  guard_target = n = answer_forall_bound._answer n
  rfl

-- Variable bound by a fun (lambda) in the type.
-- When elaborating `fun (n : Nat) => answer(n)`, `n` is a lambda fvar.
theorem answer_fun_bound : (fun (n : Nat) => answer(n)) = id := by
  run_tac Tactic.withMainContext do
    let env ← getEnv
    let some _ := env.find? `answer_fun_bound._answer | throwError "auxiliary not found"
  guard_target = (fun n => answer_fun_bound._answer n) = id
  rfl

-- Mix of a theorem parameter (α) and a ∀-bound variable (a).
-- The auxiliary must be abstracted over both, with α first in declaration order.
theorem answer_param_and_forall (α : Type) : ∀ (a : α), a = answer(a) := by
  run_tac Tactic.withMainContext do
    let env ← getEnv
    let some _ := env.find? `answer_param_and_forall._answer | throwError "auxiliary not found"
  intro a
  guard_target = a = answer_param_and_forall._answer α a
  rfl

-- fun outer, ∀ inner: `n` is bound by the outer fun, `m` by the inner ∀,
-- and `answer(n + m)` sees both.
theorem answer_fun_then_forall :
    (fun (n : Nat) => ∀ (m : Nat), answer(n + m) = n + m) = (fun n => ∀ m, n + m = n + m) := by
  run_tac Tactic.withMainContext do
    let env ← getEnv
    let some _ := env.find? `answer_fun_then_forall._answer | throwError "auxiliary not found"
  guard_target =
    (fun n => ∀ m, answer_fun_then_forall._answer n m = n + m) = (fun n => ∀ m, n + m = n + m)
  rfl

-- ∀ outer, fun inner: `n` is bound by the outer ∀, `m` by the inner fun,
-- and `answer(n + m)` sees both.
theorem answer_forall_then_fun :
    ∀ (n : Nat), (fun (m : Nat) => answer(n + m)) = (fun m => n + m) := by
  run_tac Tactic.withMainContext do
    let env ← getEnv
    let some _ := env.find? `answer_forall_then_fun._answer | throwError "auxiliary not found"
  intro n
  guard_target = (fun m => answer_forall_then_fun._answer n m) = (fun m => n + m)
  rfl

end WithAuxiliary

section AlwaysTrue

set_option google.answer "always_true"

theorem this_works : (answer(sorry) : Prop) := by
  trivial

end AlwaysTrue
