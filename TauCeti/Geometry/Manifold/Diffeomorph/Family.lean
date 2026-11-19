/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Smooth families of diffeomorphisms

Let `f p : M ≃ₘ^n⟮I, J⟯ N` be a family of `C^n` diffeomorphisms, `1 ≤ n`, indexed by the points
`p` of a manifold `P`, which is jointly `C^n`: `(p, x) ↦ f p x` is `C^n` on `P × M`. Then the
family of inverses `(p, y) ↦ (f p)⁻¹ y` is jointly `C^n` as well
(`Diffeomorph.contMDiff_symm_family`), and the fibre-preserving map `(p, x) ↦ (p, f p x)` is a
`C^n` diffeomorphism of `P × M` onto `P × N` (`Diffeomorph.prodCongrRight`), whose inverse is the
map `(p, y) ↦ (p, (f p)⁻¹ y)` of the inverse family. This is the smooth counterpart of
`Equiv.prodCongrRight`; `Diffeomorph.prodCongrLeft` is the counterpart of `Equiv.prodCongrLeft`,
with the parameter in the second factor, `(x, p) ↦ (f p x, p)`. Smoothness of each inverse
`(f p)⁻¹` separately does not give joint smoothness of the inverse family: the derivative of
`(p, y) ↦ (f p)⁻¹ y` in the parameter direction also involves the parameter derivative of `f`.
So a construction that modifies a product map fibre by fibre, through diffeomorphisms of the
fibres depending smoothly on a parameter, yields a diffeomorphism of the total space.

The proof is the inverse function theorem
(`TauCeti.isLocalDiffeomorph_of_mfderiv_eq`). For a jointly `C^n` map `φ : P × M → N`, the
differential of `F (p, x) = (p, φ (p, x))` at `z` is block triangular,

`(u, v) ↦ (u, A u + B v)`,

where `A` and `B` are the differentials of `φ` in the parameter and in the fibre. When `B` is
invertible, so is this map (`ContinuousLinearMap.isInvertible_iff_of_fst_comp_eq`), with inverse
`(u, w) ↦ (u, B⁻¹ (w - A u))`; this needs no finite-dimensionality. So `F` is a local
diffeomorphism as soon as the differential of every slice `x ↦ φ (p, x)` is invertible
(`TauCeti.isLocalDiffeomorph_fst_prodMk`), and a bijective local diffeomorphism is a
diffeomorphism (`IsLocalDiffeomorph.diffeomorphOfBijective`). The inverse function theorem is
applied at every point of `P × M`, so `P` and `M` are boundaryless.

## Main results

* `TauCeti.isLocalDiffeomorph_fst_prodMk`: if `φ` is `C^n` and every slice `x ↦ φ (p, x)` has
  invertible differentials, then `(p, x) ↦ (p, φ (p, x))` is a `C^n` local diffeomorphism.
* `Diffeomorph.contMDiff_symm_family`: the inverses of a jointly `C^n` family of diffeomorphisms
  form a jointly `C^n` family.
* `Diffeomorph.prodCongrRight`, `Diffeomorph.prodCongrLeft`: the diffeomorphisms
  `(p, x) ↦ (p, f p x)` and `(x, p) ↦ (f p x, p)` of a jointly `C^n` family `f`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 4.5 (the inverse function theorem for manifolds).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications **52**, 2012, proof of Theorem 9.4.7 (diffeomorphisms of `S² × S²` assembled from
  families of diffeomorphisms of the fibres).
-/

public section

open scoped Manifold ContDiff

variable {𝕂 : Type*} [RCLike 𝕂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕂 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕂 E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕂 E' H'}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕂 F G}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}
  [IsManifold I' n P] [IsManifold I n M] [IsManifold J n N]
  [BoundarylessManifold I' P] [BoundarylessManifold I M]

namespace TauCeti

/-- **A map with invertible fibre differentials, paired with the parameter, is a local
diffeomorphism.** If `φ : P × M → N` is `C^n`, `1 ≤ n`, and every slice `x ↦ φ (p, x)` has
invertible differentials, then `(p, x) ↦ (p, φ (p, x))` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_fst_prodMk {φ : P × M → N} (hφ : ContMDiff (I'.prod I) J n φ)
    (hn : 1 ≤ n) (hφ' : ∀ z : P × M, (mfderiv I J (fun x ↦ φ (z.1, x)) z.2).IsInvertible) :
    IsLocalDiffeomorph (I'.prod I) (I'.prod J) n fun z : P × M ↦ (z.1, φ z) := by
  refine isLocalDiffeomorph_of_mfderiv_eq (contMDiff_fst.prodMk hφ) hn fun z ↦ ?_
  have hdiff : MDifferentiableAt (I'.prod I) J φ z := hφ.mdifferentiableAt (by
    rintro rfl
    exact absurd hn (by simp))
  -- Read the differential as a map between the model spaces of the charts.
  obtain ⟨T, hT⟩ : ∃ T : E' × E →L[𝕂] E' × F,
      mfderiv (I'.prod I) (I'.prod J) (fun z : P × M ↦ (z.1, φ z)) z = T := ⟨_, rfl⟩
  have hd (v : E' × E) : T v = (v.1, mfderiv (I'.prod I) J φ z v) := by
    rw [← hT, mfderiv_prodMk mdifferentiableAt_fst hdiff, mfderiv_fst]
    -- This is `prod_apply`, read through `TangentSpace` being the model space.
    exact ContinuousLinearMap.prod_apply _ _ v
  -- The differential keeps the parameter coordinate and acts on the fibre by the slice
  -- differential, so it is invertible exactly when the slice differential is.
  have hfst : ContinuousLinearMap.fst 𝕂 E' F ∘L T = ContinuousLinearMap.fst 𝕂 E' E :=
    ContinuousLinearMap.ext fun v ↦ by simp [hd]
  have hblock : ContinuousLinearMap.snd 𝕂 E' F ∘L T ∘L ContinuousLinearMap.inr 𝕂 E' E =
      mfderiv I J (fun x ↦ φ (z.1, x)) z.2 :=
    ContinuousLinearMap.ext fun v ↦ by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hd,
        ContinuousLinearMap.coe_snd']
      -- Only the fibre term of `mfderiv_prod_eq_add_apply` survives on `inr v = (0, v)`.
      calc mfderiv (I'.prod I) J φ z (0, v)
          = mfderiv I' J (fun p ↦ φ (p, z.2)) z.1 0 + mfderiv I J (fun x ↦ φ (z.1, x)) z.2 v :=
            mfderiv_prod_eq_add_apply hdiff
        _ = mfderiv I J (fun x ↦ φ (z.1, x)) z.2 v := by rw [map_zero, zero_add]
  rw [hT]
  exact (ContinuousLinearMap.isInvertible_iff_of_fst_comp_eq hfst).2 (hblock ▸ hφ' z)

end TauCeti

namespace Diffeomorph

variable {f : P → M ≃ₘ^n⟮I, J⟯ N}

/-- **The inverses of a smooth family of diffeomorphisms form a smooth family.** If
`(p, x) ↦ f p x` is `C^n` on `P × M`, `1 ≤ n`, then so is `(p, y) ↦ (f p)⁻¹ y` on `P × N`. -/
theorem contMDiff_symm_family (hf : ContMDiff (I'.prod I) J n fun z : P × M ↦ f z.1 z.2)
    (hn : 1 ≤ n) : ContMDiff (I'.prod J) I n fun z : P × N ↦ (f z.1).symm z.2 := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact absurd hn (by simp)
  let e : P × M ≃ P × N := Equiv.prodCongrRight fun p ↦ (f p).toEquiv
  let Φ := (TauCeti.isLocalDiffeomorph_fst_prodMk hf hn fun z ↦
    (f z.1).isInvertible_mfderiv hn0).diffeomorphOfBijective e.bijective
  -- `Φ` is `e` as a map, so its inverse is `e.symm`, whose second component is the family.
  have hΦ (z : P × N) : Φ.symm z = e.symm z := by
    have h : Φ (e.symm z) = z :=
      (congrFun (IsLocalDiffeomorph.coe_diffeomorphOfBijective _ _) _).trans (e.apply_symm_apply z)
    calc Φ.symm z = Φ.symm (Φ (e.symm z)) := by rw [h]
      _ = e.symm z := Φ.symm_apply_apply _
  exact (contMDiff_snd.comp Φ.symm.contMDiff).congr fun z ↦ by simp [hΦ, e]

/-- **A smooth family of diffeomorphisms is a diffeomorphism of the product.** For a family
`f p : M ≃ₘ^n⟮I, J⟯ N` such that `(p, x) ↦ f p x` is `C^n` on `P × M`, `1 ≤ n`, the map
`(p, x) ↦ (p, f p x)` is a `C^n` diffeomorphism of `P × M` onto `P × N`. Its inverse is
`(p, y) ↦ (p, (f p)⁻¹ y)` (`Diffeomorph.prodCongrRight_symm_apply`). This is the smooth
counterpart of `Equiv.prodCongrRight`. -/
def prodCongrRight (f : P → M ≃ₘ^n⟮I, J⟯ N)
    (hf : ContMDiff (I'.prod I) J n fun z : P × M ↦ f z.1 z.2) (hn : 1 ≤ n) :
    (P × M) ≃ₘ^n⟮I'.prod I, I'.prod J⟯ (P × N) where
  toEquiv := Equiv.prodCongrRight fun p ↦ (f p).toEquiv
  contMDiff_toFun := contMDiff_fst.prodMk hf
  contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_symm_family hf hn)

variable (hf : ContMDiff (I'.prod I) J n fun z : P × M ↦ f z.1 z.2) (hn : 1 ≤ n)

@[simp]
theorem coe_prodCongrRight : ⇑(prodCongrRight f hf hn) = fun z ↦ (z.1, f z.1 z.2) :=
  (rfl)

@[simp]
theorem prodCongrRight_apply (p : P) (x : M) : prodCongrRight f hf hn (p, x) = (p, f p x) :=
  (rfl)

@[simp]
theorem toEquiv_prodCongrRight :
    (prodCongrRight f hf hn).toEquiv = Equiv.prodCongrRight fun p ↦ (f p).toEquiv :=
  (rfl)

@[simp]
theorem prodCongrRight_symm_apply (p : P) (y : N) :
    (prodCongrRight f hf hn).symm (p, y) = (p, (f p).symm y) :=
  (rfl)

/-- **A smooth family of diffeomorphisms, with the parameter in the second factor, is a
diffeomorphism of the product.** For a family `f p : M ≃ₘ^n⟮I, J⟯ N` such that
`(x, p) ↦ f p x` is `C^n` on `M × P`, `1 ≤ n`, the map `(x, p) ↦ (f p x, p)` is a `C^n`
diffeomorphism of `M × P` onto `N × P`, with inverse `(y, p) ↦ ((f p)⁻¹ y, p)`. This is the smooth
counterpart of `Equiv.prodCongrLeft`. -/
def prodCongrLeft (f : P → M ≃ₘ^n⟮I, J⟯ N)
    (hf : ContMDiff (I.prod I') J n fun z : M × P ↦ f z.2 z.1) (hn : 1 ≤ n) :
    (M × P) ≃ₘ^n⟮I.prod I', J.prod I'⟯ (N × P) where
  toEquiv := Equiv.prodCongrLeft fun p ↦ (f p).toEquiv
  contMDiff_toFun := hf.prodMk contMDiff_snd
  contMDiff_invFun :=
    ((contMDiff_symm_family (hf.comp (contMDiff_snd.prodMk contMDiff_fst)) hn).comp
      (contMDiff_snd.prodMk contMDiff_fst)).prodMk contMDiff_snd

variable (hf' : ContMDiff (I.prod I') J n fun z : M × P ↦ f z.2 z.1)

@[simp]
theorem coe_prodCongrLeft : ⇑(prodCongrLeft f hf' hn) = fun z ↦ (f z.2 z.1, z.2) :=
  (rfl)

@[simp]
theorem prodCongrLeft_apply (x : M) (p : P) : prodCongrLeft f hf' hn (x, p) = (f p x, p) :=
  (rfl)

@[simp]
theorem toEquiv_prodCongrLeft :
    (prodCongrLeft f hf' hn).toEquiv = Equiv.prodCongrLeft fun p ↦ (f p).toEquiv :=
  (rfl)

@[simp]
theorem prodCongrLeft_symm_apply (y : N) (p : P) :
    (prodCongrLeft f hf' hn).symm (y, p) = ((f p).symm y, p) :=
  (rfl)

@[simp]
theorem prodCongrLeft_trans_prodComm :
    (prodCongrLeft f hf' hn).trans (prodComm J I' N P n) =
      (prodComm I I' M P n).trans
        (prodCongrRight f (hf'.comp (contMDiff_snd.prodMk contMDiff_fst)) hn) :=
  Diffeomorph.ext fun _ ↦ rfl

@[simp]
theorem prodCongrRight_trans_prodComm :
    (prodCongrRight f hf hn).trans (prodComm I' J P N n) =
      (prodComm I' I P M n).trans
        (prodCongrLeft f (hf.comp (contMDiff_snd.prodMk contMDiff_fst)) hn) :=
  Diffeomorph.ext fun _ ↦ rfl

section Symm

/-! The inverse of a family diffeomorphism is the diffeomorphism of the inverse family; this
needs the inverse family's hypotheses, a complete model and a boundaryless manifold `N`. -/

variable [CompleteSpace F] [BoundarylessManifold J N]

@[simp]
theorem prodCongrRight_symm :
    (prodCongrRight f hf hn).symm =
      prodCongrRight (fun p ↦ (f p).symm) (contMDiff_symm_family hf hn) hn :=
  (rfl)

@[simp]
theorem prodCongrLeft_symm :
    (prodCongrLeft f hf' hn).symm =
      prodCongrLeft (fun p ↦ (f p).symm)
        ((contMDiff_symm_family (hf'.comp (contMDiff_snd.prodMk contMDiff_fst)) hn).comp
          (contMDiff_snd.prodMk contMDiff_fst)) hn :=
  (rfl)

end Symm

end Diffeomorph
