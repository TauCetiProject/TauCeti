/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Cayley
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Sylvester
import TauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions

/-!
# Rosenblum's theorem for self-adjoint partial linear maps

Let `A` and `B` be self-adjoint, possibly unbounded, operators on complex Hilbert spaces `E` and
`F`, and let `X : E →L[ℂ] F` be a bounded operator intertwining them in the domain-aware sense
`X A ⊆ B X` (`LinearPMap.Intertwines`). **Rosenblum's theorem** says that if the spectra of `A`
and `B` are disjoint, then `X = 0`. Equivalently, the domain-aware Sylvester equation
`A X - X B = C` has at most one bounded solution.

The proof passes to the Cayley transforms `U_A` and `U_B`, which are unitary and are intertwined
by `X`, so that `X f(U_A) = f(U_B) X` for every symbol `f` continuous on both spectra
(`LinearPMap.Intertwines.comp_cfc_cayley_eq`). By spectral mapping for the Cayley transform
(`LinearPMap.mem_spectrum_cayley_iff`), disjointness of the spectra of `A` and `B` means that the
spectra of `U_A` and `U_B` meet at most in the point `1`, the image of infinity. The symbol which
is `1 - z` on the spectrum of `U_A` and `0` on that of `U_B` is therefore continuous on both
spectra, since the two prescriptions agree at `1`. It gives `X (1 - U_A) = 0`. The range of
`1 - U_A` is the domain of `A`, which is dense, so `X = 0`. No spectral measure is needed, and
both spectra may be unbounded.

Viewing bounded self-adjoint operators as partial linear maps with full domain specializes this
to the bounded Rosenblum theorem.

## Main results

* `LinearPMap.Intertwines.eq_zero_of_disjoint_spectrum`: Rosenblum's theorem for self-adjoint
  partial linear maps.
* `LinearPMap.SylvesterEquation.eq_of_disjoint_spectrum`: uniqueness of solutions of the
  domain-aware Sylvester equation when the spectra are disjoint.
* `ContinuousLinearMap.eq_zero_of_comp_eq_comp_of_disjoint_spectrum`: Rosenblum's theorem for
  bounded self-adjoint operators.

## References

* M. Rosenblum, *On the operator equation BX − XA = Q*, Duke Math. J. **23** (1956), 263–269.
* R. Bhatia, P. Rosenthal, *How and why to solve the operator equation AX − XB = Y*,
  Bull. London Math. Soc. **29** (1997), 1–21.
-/

public section

noncomputable section

open Complex

namespace LinearPMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Rosenblum's theorem.** A bounded operator intertwining two self-adjoint partial linear maps
with disjoint spectra is zero. -/
theorem Intertwines.eq_zero_of_disjoint_spectrum {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    {X : E →L[ℂ] F} (h : A.Intertwines B X) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAB : Disjoint A.spectrum B.spectrum) : X = 0 := by
  have hA' : -I ∈ A.resolventSet := hA.mem_resolventSet_of_im_ne_zero (by simp)
  have hB' : -I ∈ B.resolventSet := hB.mem_resolventSet_of_im_ne_zero (by simp)
  have := hA.isStarNormal_cayley
  -- The spectra of the Cayley transforms meet at most in `1`.
  have hsep : ∀ z ∈ _root_.spectrum ℂ A.cayley, z ∈ _root_.spectrum ℂ B.cayley → z = 1 := by
    refine fun z hzA hzB => by_contra fun hz => ?_
    exact hAB.ne_of_mem ((mem_spectrum_cayley_iff hA' hz).mp hzA)
      ((mem_spectrum_cayley_iff hB' hz).mp hzB) rfl
  -- The symbol `1 - z` on `σ(U_A)` and `0` on `σ(U_B)` gives `X (1 - U_A) = 0`.
  let f : ℂ → ℂ := (_root_.spectrum ℂ B.cayley)ᶜ.indicator fun z => 1 - z
  have hfA : (_root_.spectrum ℂ A.cayley).EqOn f (fun z => 1 - z) := fun z hz => by
    by_cases hzB : z ∈ _root_.spectrum ℂ B.cayley
    · simp [f, hsep z hz hzB]
    · simp [f, hzB]
  have hfB : (_root_.spectrum ℂ B.cayley).EqOn f 0 := fun z hz => by simp [f, hz]
  have hX := h.comp_cfc_cayley_eq hA hB f
    ((continuousOn_const.sub continuousOn_id).congr hfA) (continuousOn_const.congr hfB)
  rw [cfc_congr hfA, cfc_congr hfB] at hX
  simp [cfc_sub (fun _ : ℂ => (1 : ℂ)) (fun z : ℂ => z) A.cayley, cfc_const_one ℂ A.cayley,
    cfc_id' ℂ A.cayley] at hX
  -- `X` vanishes on the dense domain of `A`, which is the range of `1 - U_A`.
  refine DFunLike.coe_injective <| X.continuous.ext_on hA.dense_domain continuous_const
    fun y hy => ?_
  obtain ⟨x, hx⟩ := (mem_graph_iff_exists_cayley hA').mp (A.mem_graph ⟨y, hy⟩)
  have hxy : x - A.cayley x = y := (Prod.mk.inj hx).1
  rw [← hxy]
  simpa using DFunLike.congr_fun hX x

/-- **Uniqueness for the Sylvester equation.** If self-adjoint partial linear maps `A` and `B`
have disjoint spectra, the domain-aware Sylvester equation `A X - X B = C` has at most one
bounded solution `X`. -/
theorem SylvesterEquation.eq_of_disjoint_spectrum {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    {X Y C : F →L[ℂ] E} (hX : SylvesterEquation A B X C) (hY : SylvesterEquation A B Y C)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hAB : Disjoint A.spectrum B.spectrum) :
    X = Y := by
  have h := hX.sub hY
  rw [sub_self, sylvesterEquation_zero_iff_intertwines] at h
  exact sub_eq_zero.mp (h.eq_zero_of_disjoint_spectrum hB hA hAB.symm)

end LinearPMap

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Rosenblum's theorem for bounded operators.** If bounded self-adjoint operators `S` and `T`
have disjoint spectra, the only bounded operator `X` with `X S = T X` is zero. -/
theorem eq_zero_of_comp_eq_comp_of_disjoint_spectrum {S : E →L[ℂ] E} {T : F →L[ℂ] F}
    {X : E →L[ℂ] F} (h : X ∘L S = T ∘L X) (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    (hST : Disjoint (spectrum ℂ S) (spectrum ℂ T)) : X = 0 :=
  ((intertwines_toPMap_top_iff S T X).mpr h).eq_zero_of_disjoint_spectrum
    (LinearPMap.isSelfAdjoint_toPMap_top hS) (LinearPMap.isSelfAdjoint_toPMap_top hT)
    (by simpa using hST)

end ContinuousLinearMap
