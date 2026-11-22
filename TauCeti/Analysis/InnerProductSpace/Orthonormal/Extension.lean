/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# Extending orthonormal frames

In an inner product space of dimension at least four, every orthonormal pair extends to an
orthonormal four-frame (`Orthonormal.exists_fin_four_extension`). In a space of dimension `n + 1`,
every unit vector is the first vector of an orthonormal basis indexed by `Fin (n + 1)`
(`TauCeti.exists_orthonormalBasis_fin_apply_zero_eq`).
-/

public section

namespace Orthonormal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- In dimension at least four, every orthonormal pair `![u, v]` extends to an orthonormal
four-frame `f` with `f 0 = u` and `f 2 = v`. -/
theorem exists_fin_four_extension {u v : E} (huv : Orthonormal 𝕜 ![u, v])
    (hn : 4 ≤ Module.finrank 𝕜 E) :
    ∃ f : Fin 4 → E, Orthonormal 𝕜 f ∧ f 0 = u ∧ f 2 = v := by
  classical
  obtain ⟨w₁, hw₁, hw₁o⟩ := TauCeti.exists_norm_eq_one_forall_inner_eq_zero_of_card_lt_finrank
    (𝕜 := 𝕜) ({u, v} : Finset E) (Finset.card_le_two.trans_lt (by omega))
  obtain ⟨w₂, hw₂, hw₂o⟩ := TauCeti.exists_norm_eq_one_forall_inner_eq_zero_of_card_lt_finrank
    (𝕜 := 𝕜) ({u, v, w₁} : Finset E) (Finset.card_le_three.trans_lt (by omega))
  have hu : ‖u‖ = 1 := huv.1 0; have hv : ‖v‖ = 1 := huv.1 1
  have huv0 : inner 𝕜 u v = 0 := huv.2 (by decide : (0 : Fin 2) ≠ 1)
  refine ⟨![u, w₁, v, w₂], ?_, rfl, rfl⟩
  simp [Fin.forall_fin_succ, hu, hv, huv0, hw₁, hw₂, hw₁o u (by simp),
    inner_eq_zero_symm.2 (hw₁o v (by simp)), hw₂o u (by simp), hw₂o v (by simp), hw₂o w₁ (by simp)]

end Orthonormal

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- In a space of dimension `n + 1`, every unit vector `e` is the first vector of an orthonormal
basis indexed by `Fin (n + 1)`. -/
theorem exists_orthonormalBasis_fin_apply_zero_eq {n : ℕ} (hn : Module.finrank 𝕜 E = n + 1)
    {e : E} (he : ‖e‖ = 1) : ∃ b : OrthonormalBasis (Fin (n + 1)) 𝕜 E, b 0 = e := by
  have : FiniteDimensional 𝕜 E := Module.finite_of_finrank_eq_succ hn
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := 𝕜)
    (ι := Fin (n + 1)) (by simp [hn]) (v := fun _ ↦ e) (s := {0}) <| by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      simp only [Set.mem_singleton_iff] at hi hj
      subst hi hj
      simp [he]
  exact ⟨b, hb 0 rfl⟩

end TauCeti
