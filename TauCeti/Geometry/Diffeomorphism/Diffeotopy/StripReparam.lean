/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.Diffeomorph.StripReparam

/-!
# Strip reparametrizations along a family form a diffeotopy

Let `U ⊆ M` be open and `F` a `C^n` diffeomorphism of `M × M` which, together with its inverse,
preserves the strip leaves over `U` (`TauCeti.PreservesStripLeaves`). A family `ρ t`,
`t ∈ [0, 1]`, of self-maps of `M` mapping `U` into itself, fixing every point outside a closed
subset `K ⊆ U` and starting at `ρ 0 = id`, gives a diffeotopy of `M × M` carrying `F` to its
strip reparametrization (`TauCeti.stripReparam`) by `ρ t` at time `t`
(`TauCeti.Diffeotopy.stripReparam`, `TauCeti.Diffeotopy.timeSlice_stripReparam_apply`). For a
radial map `ρ` the straight-line interpolations `x ↦ (1 - t) x + t ρ x` in a disc chart are such
a family.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, proof of Theorem 9.4.7 (ii).
-/

public section

open Set Function
open scoped Manifold ContDiff

namespace TauCeti.Diffeotopy

open unitInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω} {U K : Set M} {ρ : I → M → M}

/-- **Strip reparametrizations along a family form an isotopy.** Let `U ⊆ M` be open and `F` a
`C^n` diffeomorphism of `M × M` which, together with its inverse, preserves the strip leaves over
`U`. Let `ρ t`, for `t ∈ [0, 1]`, be self-maps of `M` depending jointly `C^n`-smoothly on `t` and
the point, each mapping `U` into itself and fixing every point outside a closed subset `K ⊆ U`,
with `ρ 0 = id`. Then the maps `stripReparam U (ρ t) F ∘ F⁻¹` form a diffeotopy of `M × M`, so
the reparametrization of `F` by `ρ t` is the diffeotopy at time `t` composed with `F`
(`TauCeti.Diffeotopy.timeSlice_stripReparam_apply`). -/
noncomputable def stripReparam (F : (M × M) ≃ₘ^n⟮J.prod J, J.prod J⟯ (M × M))
    (hF : PreservesStripLeaves U F) (hF' : PreservesStripLeaves U F.symm) (hU : IsOpen U)
    (hK : IsClosed K) (hKU : K ⊆ U) (hρ : ContMDiff ((𝓡∂ 1).prod J) J n fun q : I × M ↦ ρ q.1 q.2)
    (hρK : ∀ t, ∀ x ∉ K, ρ t x = x) (hρU : ∀ t, MapsTo (ρ t) U U) (hρ₀ : ρ 0 = id) :
    Diffeotopy (J.prod J) n (M × M) where
  toDiffeomorph :=
    { toFun := fun q ↦ (q.1, TauCeti.stripReparam U (ρ q.1) F (F.symm q.2))
      invFun := fun q ↦ (q.1, F (TauCeti.stripReparam U (ρ q.1) F.symm q.2))
      left_inv := fun q ↦ by
        simp only [leftInverse_stripReparam hF' hF (hρU _) F.symm_apply_apply _,
          F.apply_symm_apply]
      right_inv := fun q ↦ by
        simp only [F.symm_apply_apply, leftInverse_stripReparam hF hF' (hρU _) F.apply_symm_apply _]
      contMDiff_toFun := contMDiff_fst.prodMk
        ((contMDiff_stripReparam hU hK hKU hρ hρK F.contMDiff hF).comp
          (contMDiff_fst.prodMk (F.symm.contMDiff.comp contMDiff_snd)))
      contMDiff_invFun := contMDiff_fst.prodMk (F.contMDiff.comp
        ((contMDiff_stripReparam hU hK hKU hρ hρK F.symm.contMDiff hF').comp
          (contMDiff_fst.prodMk contMDiff_snd))) }
  fst_apply _ := rfl
  snd_apply_zero' x := by
    rw [← Diffeomorph.coe_toEquiv, Equiv.coe_fn_mk, hρ₀, stripReparam_id hF, F.apply_symm_apply]

variable (F : (M × M) ≃ₘ^n⟮J.prod J, J.prod J⟯ (M × M)) (hF : PreservesStripLeaves U F)
  (hF' : PreservesStripLeaves U F.symm) (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
  (hρ : ContMDiff ((𝓡∂ 1).prod J) J n fun q : I × M ↦ ρ q.1 q.2)
  (hρK : ∀ t, ∀ x ∉ K, ρ t x = x) (hρU : ∀ t, MapsTo (ρ t) U U) (hρ₀ : ρ 0 = id)

@[simp]
theorem stripReparam_apply (p : I × (M × M)) :
    stripReparam F hF hF' hU hK hKU hρ hρK hρU hρ₀ p =
      TauCeti.stripReparam U (ρ p.1) F (F.symm p.2) :=
  (rfl)

/-- The inverse of the underlying diffeomorphism composes `F` with the reparametrization of
`F.symm`. -/
@[simp]
theorem stripReparam_toDiffeomorph_symm_apply (p : I × (M × M)) :
    (stripReparam F hF hF' hU hK hKU hρ hρK hρU hρ₀).toDiffeomorph.symm p =
      (p.1, F (TauCeti.stripReparam U (ρ p.1) F.symm p.2)) :=
  (rfl)

/-- The inverse diffeotopy composes `F` with the reparametrization of `F.symm`. -/
theorem symm_stripReparam_apply (p : I × (M × M)) :
    (stripReparam F hF hF' hU hK hKU hρ hρK hρU hρ₀).symm p =
      F (TauCeti.stripReparam U (ρ p.1) F.symm p.2) := by
  rw [symm_apply, stripReparam_toDiffeomorph_symm_apply]

/-- The diffeotopy at time `t` composed with `F` is the reparametrization of `F` by `ρ t`; in
particular it connects `F`, at time `0`, to its reparametrization by `ρ 1`. -/
theorem timeSlice_stripReparam_apply (t : I) (x : M × M) :
    (stripReparam F hF hF' hU hK hKU hρ hρK hρU hρ₀).timeSlice t (F x) =
      TauCeti.stripReparam U (ρ t) F x := by
  rw [timeSlice_apply, stripReparam_apply, F.symm_apply_apply]

/-- The inverse of the diffeotopy at time `t` is `F` composed with the reparametrization of
`F.symm` by `ρ t`. -/
theorem symm_timeSlice_stripReparam_apply (t : I) (x : M × M) :
    ((stripReparam F hF hF' hU hK hKU hρ hρK hρU hρ₀).timeSlice t).symm x =
      F (TauCeti.stripReparam U (ρ t) F.symm x) := by
  rw [symm_timeSlice_apply, symm_stripReparam_apply]

end TauCeti.Diffeotopy
