import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_587 :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 28]⟩], output := 29 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 20 ∧ (∃ A : Finset ℕ, A.card = 14 ∧ ∀ j : ℕ, j ∈ A ↔ ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (∀ x : Fin 10 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 10, (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (6, 8), (7, 9), (8, 5), (9, 6)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C hC
  subst hC
  refine ⟨?_, rfl, ⟨{0, 1, 2, 3, 4, 5, 6, 8, 9, 14, 16, 17, 18, 19}, by decide, ?_⟩, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · intro j
    by_cases hj : j < 20
    · interval_cases j <;> simp
    · rw [List.getElem?_eq_none (by simp; omega)]
      simp
      omega
  · simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
    decide +kernel
