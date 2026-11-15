/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.IdealLocus
public import TauCeti.RingTheory.Grassmannian.Isotropic
import TauCeti.RingTheory.Grassmannian.Chart.Isotropic

/-!
# The isotropic Grassmannian

Let `ω` be a bilinear form on a module `M` over a commutative ring `R`. A point of the Grassmannian
scheme `G(k, M) = Module.Grassmannian.scheme R M k` over `Spec A` is an `A`-submodule `N` of
`A ⊗[R] M` whose quotient is finite projective of constant rank `k`
(`Module.Grassmannian.schemeHomEquiv`); it is *isotropic* when the base change `ω_A` of `ω`
vanishes on `N × N`. This file constructs the **isotropic Grassmannian**, the closed subscheme of
`G(k, M)` over which the tautological submodule is isotropic, and proves that it represents the
isotropic points: a morphism `Spec A ⟶ G(k, M)` over `Spec R` factors through it exactly when the
point it classifies is isotropic. For a nondegenerate alternating form on `R^{2m}` and quotient
rank `k = 2m - r`, this is the Grassmannian of rank-`r` isotropic subbundles. Nothing is assumed
about the form or about `2`, so this covers characteristic `2` with an actual alternating form.

The closed subscheme is the instance `Module.Grassmannian.schemeIdealLocus` of the general
construction of closed subschemes of `G(k, M)` cut out by ideals of points: isotropy is cut out by
the ideal `Module.Grassmannian.isotropicLocus` of the values of `ω_A` on `N × N`, whose formation
commutes with base change (`Module.Grassmannian.isotropicLocus_map`). Over an affine open `U` of
`G(k, M)`, the ideal of the isotropic Grassmannian is `isotropicLocus` of the point over
`Γ(G(k, M), U)` classifying the inclusion of `U`.

## Main definitions

* `Module.Grassmannian.schemeIsotropicLocus k ω`: the ideal sheaf on `G(k, M)` of the isotropic
  Grassmannian.
* `Module.Grassmannian.schemeIsotropicLocusHomEquiv k ω A`: the isotropic points of
  `G(k, A ⊗[R] M; A)` are the morphisms from `Spec A` to the isotropic Grassmannian over
  `Spec R`.

## Main results

* `Module.Grassmannian.comap_toSchemeHom_schemeIsotropicLocus`: the inverse image of the isotropic
  Grassmannian along the morphism `Spec A ⟶ G(k, M)` classifying a point `N` is the zero scheme of
  `N.isotropicLocus ω`.
* `Module.Grassmannian.schemeIsotropicLocus_le_ker_toSchemeHom_iff`: **the universal property**;
  the morphism classifying `N` factors through the isotropic Grassmannian exactly when `N` is
  isotropic for `ω_A`.
* `Module.Grassmannian.isEmpty_subscheme_schemeIsotropicLocus_of_two_mul_lt_card`: the isotropic
  Grassmannian of a form with unit Gram determinant on a free module of rank `n` is empty when
  `2 k < n`.
* `Module.Grassmannian.nonempty_subscheme_schemeIsotropicLocus_of_toMatrix_eq_J`: for a symplectic
  basis of a module of rank `2m`, it is nonempty over a nontrivial ring when `m ≤ k ≤ 2m`.
* `Module.Grassmannian.nonempty_subscheme_schemeIsotropicLocus_iff`: for a symplectic basis of a
  module of rank `2m` over a nontrivial ring, it is nonempty exactly when `m ≤ k ≤ 2m`.

For a form with unit Gram determinant on a free module of rank `n`, the isotropic Grassmannian of
quotient rank `k` is empty when `2 k < n`, since its points over residue fields would be isotropic
subspaces of more than half the dimension
(`Module.Grassmannian.isEmpty_subscheme_schemeIsotropicLocus_of_two_mul_lt_card`); it is also empty
when `k > n`, since a quotient of an `n`-dimensional space has dimension at most `n`. For a
symplectic basis of a module of rank `2m`, the base point of the standard isotropic chart shows that
it is nonempty over a nontrivial ring when `m ≤ k ≤ 2m`
(`Module.Grassmannian.nonempty_subscheme_schemeIsotropicLocus_of_toMatrix_eq_J`), and this range is
sharp (`Module.Grassmannian.nonempty_subscheme_schemeIsotropicLocus_iff`). With `k = 2m - r`, the
Grassmannian of rank-`r` isotropic subbundles of a symplectic module of rank `2m` over a nontrivial
ring is empty exactly when `r > m`.

For `M` finite over `R`, the isotropic Grassmannian is proper over `Spec R` by instance inference,
as a closed subscheme of the proper Grassmannian scheme (`Module.Grassmannian.isProper_toSpec`).

## References

* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7, for
  closed conditions on the Grassmannian.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Scheme.IdealSheafData

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M] {k : ℕ}

variable (k) in
/-- The ideal sheaf of the **isotropic Grassmannian** of a bilinear form `ω` on `M`: the closed
subscheme of the Grassmannian scheme `G(k, M)` over which the tautological submodule is isotropic
for `ω`. A morphism `Spec A ⟶ G(k, M)` over `Spec R`, classifying a point `N` of
`G(k, A ⊗[R] M; A)`, factors through this closed subscheme exactly when `N` is isotropic for the
base change of `ω` to `A`
(`Module.Grassmannian.schemeIsotropicLocus_le_ker_toSchemeHom_iff`). Over an affine open `U`, its
ideal is `Module.Grassmannian.isotropicLocus` of the point over `Γ(G(k, M), U)` classifying the
inclusion of `U`. -/
noncomputable def schemeIsotropicLocus (ω : LinearMap.BilinForm R M) :
    (scheme R M k).IdealSheafData :=
  schemeIdealLocus (R := R) (M := M) (k := k) (fun N ↦ N.isotropicLocus ω)
    fun f N ↦ isotropicLocus_map f N ω

/-- **The inverse image of the isotropic Grassmannian along a point.** For an `R`-algebra `A` and
a point `N` of `G(k, A ⊗[R] M; A)`, the inverse image of the isotropic Grassmannian along the
morphism `Spec A ⟶ G(k, M)` classifying `N` is the zero scheme of `N.isotropicLocus ω`. -/
theorem comap_toSchemeHom_schemeIsotropicLocus (ω : LinearMap.BilinForm R M) {A : Type u}
    [CommRing A] [Algebra R A] (N : G(k, A ⊗[R] M; A)) :
    (schemeIsotropicLocus k ω).comap (toSchemeHom N) =
      ofIdealTop ((N.isotropicLocus ω).map (Scheme.ΓSpecIso (.of A)).inv.hom) :=
  comap_toSchemeHom_schemeIdealLocus (R := R) (M := M) (k := k) (fun N ↦ N.isotropicLocus ω)
    (fun f N ↦ isotropicLocus_map f N ω) N

/-- **The universal property of the isotropic Grassmannian.** For an `R`-algebra `A`, the
morphism `Spec A ⟶ G(k, M)` classifying a point `N` of `G(k, A ⊗[R] M; A)` factors through the
isotropic Grassmannian exactly when `N` is isotropic for the base change `ω_A` of `ω`, that is,
when `N` lies in its own orthogonal for `ω_A`. -/
theorem schemeIsotropicLocus_le_ker_toSchemeHom_iff (ω : LinearMap.BilinForm R M) {A : Type u}
    [CommRing A] [Algebra R A] (N : G(k, A ⊗[R] M; A)) :
    schemeIsotropicLocus k ω ≤ (toSchemeHom N).ker ↔
      N.toSubmodule ≤ (ω.baseChange A).orthogonal N.toSubmodule :=
  (schemeIdealLocus_le_ker_toSchemeHom_iff (R := R) (M := M) (k := k)
    (fun N ↦ N.isotropicLocus ω) (fun f N ↦ isotropicLocus_map f N ω) N).trans
    (isotropicLocus_eq_bot_iff N ω)

variable (k) in
/-- **The isotropic Grassmannian represents the isotropic points of the Grassmannian.** For an
`R`-algebra `A`, the points `N` of `G(k, A ⊗[R] M; A)` which are isotropic for the base change
`ω_A` of `ω` are in bijection with the morphisms from `Spec A` to the isotropic Grassmannian over
`Spec R`. The bijection composes with the inclusion into `G(k, M)` to the morphism classifying `N`
(`Module.Grassmannian.schemeIsotropicLocusHomEquiv_apply_comp_subschemeι` and
`Module.Grassmannian.toSchemeHom_schemeIsotropicLocusHomEquiv_symm_apply`). -/
noncomputable def schemeIsotropicLocusHomEquiv (ω : LinearMap.BilinForm R M) (A : Type u)
    [CommRing A] [Algebra R A] :
    {N : G(k, A ⊗[R] M; A) // N.toSubmodule ≤ (ω.baseChange A).orthogonal N.toSubmodule} ≃
      {h : Spec (.of A) ⟶ (schemeIsotropicLocus k ω).subscheme //
        h ≫ (schemeIsotropicLocus k ω).subschemeι ≫ toSpec R M k =
          Spec.map (CommRingCat.ofHom (algebraMap R A))} :=
  (Equiv.subtypeEquivRight fun N ↦ (isotropicLocus_eq_bot_iff N ω).symm).trans
    (schemeIdealLocusHomEquiv (R := R) (M := M) (k := k) (fun N ↦ N.isotropicLocus ω)
      (fun f N ↦ isotropicLocus_map f N ω) A)

/-- The morphism to the isotropic Grassmannian corresponding to an isotropic point `N`, followed by
the inclusion into the Grassmannian scheme, is the morphism classifying `N`. -/
@[reassoc (attr := simp)]
theorem schemeIsotropicLocusHomEquiv_apply_comp_subschemeι (ω : LinearMap.BilinForm R M)
    {A : Type u} [CommRing A] [Algebra R A]
    (N : {N : G(k, A ⊗[R] M; A) // N.toSubmodule ≤ (ω.baseChange A).orthogonal N.toSubmodule}) :
    (schemeIsotropicLocusHomEquiv k ω A N).1 ≫ (schemeIsotropicLocus k ω).subschemeι =
      toSchemeHom N.1 :=
  schemeIdealLocusHomEquiv_apply_comp_subschemeι (R := R) (M := M) (k := k)
    (fun N ↦ N.isotropicLocus ω) (fun f N ↦ isotropicLocus_map f N ω) _

/-- The isotropic point corresponding to a morphism `h` to the isotropic Grassmannian is the point
classified by `h` followed by the inclusion into the Grassmannian scheme. -/
@[simp]
theorem toSchemeHom_schemeIsotropicLocusHomEquiv_symm_apply (ω : LinearMap.BilinForm R M)
    {A : Type u} [CommRing A] [Algebra R A]
    (h : {h : Spec (.of A) ⟶ (schemeIsotropicLocus k ω).subscheme //
      h ≫ (schemeIsotropicLocus k ω).subschemeι ≫ toSpec R M k =
        Spec.map (CommRingCat.ofHom (algebraMap R A))}) :
    toSchemeHom ((schemeIsotropicLocusHomEquiv k ω A).symm h).1 =
      h.1 ≫ (schemeIsotropicLocus k ω).subschemeι :=
  toSchemeHom_schemeIdealLocusHomEquiv_symm_apply (R := R) (M := M) (k := k)
    (fun N ↦ N.isotropicLocus ω) (fun f N ↦ isotropicLocus_map f N ω) h

/-- A point of the isotropic Grassmannian gives, at its residue field `K`, a point of
`G(k, K ⊗[R] M; K)` that is isotropic for `ω_K`. -/
private theorem exists_field_point_le_orthogonal {ω : LinearMap.BilinForm R M}
    (x : (schemeIsotropicLocus k ω).subscheme) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra R K) (N : G(k, K ⊗[R] M; K)),
      N.toSubmodule ≤ (ω.baseChange K).orthogonal N.toSubmodule := by
  set Z := (schemeIsotropicLocus k ω).subscheme
  -- the residue field at `x` is an `R`-algebra through the structure morphism of `Z`
  let φ := Spec.preimage (Z.fromSpecResidueField x ≫ (schemeIsotropicLocus k ω).subschemeι ≫
    toSpec R M k)
  let : Algebra R (Z.residueField x) := φ.hom.toAlgebra
  obtain ⟨N, hN⟩ := (schemeIsotropicLocusHomEquiv k ω (Z.residueField x)).symm
    ⟨Z.fromSpecResidueField x, by simp [φ, RingHom.algebraMap_toAlgebra]⟩
  exact ⟨_, inferInstance, _, N, hN⟩

/-- **The isotropic Grassmannian of a large rank is empty.** Let `ω` be a bilinear form on a free
module `M` with basis `b` indexed by `ι`, whose Gram matrix has unit determinant. If `2 k < |ι|`,
the isotropic Grassmannian of quotient rank `k` is the empty scheme. For a symplectic form on
`R^{2m}` and `k = 2m - r`, this says that there are no isotropic subbundles of rank `r > m`. -/
theorem isEmpty_subscheme_schemeIsotropicLocus_of_two_mul_lt_card {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι R M) {ω : LinearMap.BilinForm R M}
    (hω : IsUnit (LinearMap.BilinForm.toMatrix b ω).det) (hk : 2 * k < Fintype.card ι) :
    IsEmpty (schemeIsotropicLocus k ω).subscheme := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨K, _, _, N, hN⟩ := exists_field_point_le_orthogonal x
  have := card_le_two_mul_of_le_orthogonal b hω hN
  omega

/-- **The isotropic Grassmannian of a symplectic module is nonempty in the expected range.** Let
`b` be a symplectic basis of `M` indexed by `ι ⊕ ι`, with Gram matrix `Matrix.J` for `ω`, so `M`
has rank `2m` with `m = |ι|`. Over a nontrivial ring, the isotropic Grassmannian of quotient rank
`k` with `m ≤ k ≤ 2m` is nonempty: relabelling `b` by `ι ≃ Fin (2m - k) ⊕ Fin (k - m)`, it has the
point over `R` given by the span of the first `2m - k` vectors `b (inl i)`, the base point of the
standard isotropic chart. -/
theorem nonempty_subscheme_schemeIsotropicLocus_of_toMatrix_eq_J [Nontrivial R] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Basis (ι ⊕ ι) R M) {ω : LinearMap.BilinForm R M}
    (hb : LinearMap.BilinForm.toMatrix b ω = Matrix.J ι R) (hk₁ : Fintype.card ι ≤ k)
    (hk₂ : k ≤ 2 * Fintype.card ι) :
    Nonempty (schemeIsotropicLocus k ω).subscheme := by
  -- relabel `b` as a symplectic basis indexed by `(Fin r ⊕ κ) ⊕ (Fin r ⊕ κ)`
  let σ : ι ≃ Fin (2 * Fintype.card ι - k) ⊕ Fin (k - Fintype.card ι) :=
    Fintype.equivOfCardEq (by simp; omega)
  let b' := b.reindex (σ.sumCongr σ)
  have hb' : LinearMap.BilinForm.toMatrix b' ω = Matrix.J _ R := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, Basis.reindex_apply, Basis.reindex_apply,
      ← LinearMap.BilinForm.toMatrix_apply, hb]
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.J, Matrix.one_apply]
  let e : Fin k ≃ Fin (k - Fintype.card ι) ⊕ (Fin (2 * Fintype.card ι - k) ⊕
      Fin (k - Fintype.card ι)) :=
    Fintype.equivFinOfCardEq (by simp; omega) |>.symm
  -- the base point of the standard isotropic chart, an isotropic point over `R`
  let N := (isotropicChartEquiv b' e R hb').symm 0
  let h := schemeIsotropicLocusHomEquiv k ω R ⟨N.1.1, (isotropicLocus_eq_bot_iff _ ω).mp N.2⟩
  obtain ⟨p⟩ : Nonempty (Spec (.of R)) := inferInstance
  exact ⟨h.1 p⟩

/-- **The nonemptiness range of the isotropic Grassmannian.** Let `b` be a symplectic basis of `M`
indexed by `ι ⊕ ι`, with Gram matrix `Matrix.J` for `ω`, so `M` has rank `2m` with `m = |ι|`. Over
a nontrivial ring, the isotropic Grassmannian of quotient rank `k` is nonempty exactly when
`m ≤ k ≤ 2m`. With `k = 2m - r`, the isotropic subbundles of rank `r` form a nonempty scheme
exactly when `r ≤ m`. -/
theorem nonempty_subscheme_schemeIsotropicLocus_iff [Nontrivial R] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis (ι ⊕ ι) R M) {ω : LinearMap.BilinForm R M}
    (hb : LinearMap.BilinForm.toMatrix b ω = Matrix.J ι R) :
    Nonempty (schemeIsotropicLocus k ω).subscheme ↔
      Fintype.card ι ≤ k ∧ k ≤ 2 * Fintype.card ι := by
  refine ⟨fun ⟨x⟩ ↦ ?_, fun h ↦
    nonempty_subscheme_schemeIsotropicLocus_of_toMatrix_eq_J b hb h.1 h.2⟩
  obtain ⟨K, _, _, N, hN⟩ := exists_field_point_le_orthogonal x
  have h₁ := card_le_two_mul_of_le_orthogonal b (hb ▸ Matrix.isUnit_det_J ι R) hN
  -- a quotient of `K ⊗[R] M` has dimension at most `2m`
  have := Module.Finite.of_basis (b.baseChange K)
  have h₂ := Submodule.finrank_quotient_le N.toSubmodule
  rw [finrank_quotient, Module.finrank_eq_card_basis (b.baseChange K)] at h₂
  simp only [Fintype.card_sum] at h₁ h₂
  omega

end Module.Grassmannian
