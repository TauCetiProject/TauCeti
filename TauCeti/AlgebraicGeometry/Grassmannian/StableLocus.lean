/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import TauCeti.AlgebraicGeometry.Grassmannian.IdealLocus
public import TauCeti.RingTheory.Grassmannian.Chart.StableLocus
public import TauCeti.RingTheory.Grassmannian.StableLocus

import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import TauCeti.Algebra.DualNumber.Basic
import TauCeti.AlgebraicGeometry.Grassmannian.Proper

/-!
# The closed subscheme of stable submodules in the Grassmannian scheme

Let `t` be an endomorphism of a module `M` over a commutative ring `R`. A point of the Grassmannian
scheme `G(k, M) = Module.Grassmannian.scheme R M k` over `Spec A` is an `A`-submodule `N` of
`A ⊗[R] M` whose quotient is finite projective of constant rank `k`
(`Module.Grassmannian.schemeHomEquiv`). This file cuts out the closed subscheme of `G(k, M)` over
which the universal submodule is stable under `t`: a morphism `Spec A ⟶ G(k, M)` over `Spec R`
factors through it exactly when the point `N` it classifies satisfies `t_A(N) ⊆ N` for the base
change `t_A` of `t`. Nothing is assumed about `R`, `M` or `t`, and the test algebras `A` may be
nonreduced, so this closed subscheme carries its natural, possibly nonreduced, scheme structure.

For `t` the multiplication by the uniformizer on the free module `X^(-N) R⟦X⟧ⁿ / X^N R⟦X⟧ⁿ` of
rank `2nN`, the points of this closed subscheme over `A` are the lattices `L` with
`X^N A⟦X⟧ⁿ ⊆ L ⊆ X^(-N) A⟦X⟧ⁿ` whose quotient `X^(-N) A⟦X⟧ⁿ / L` is finite projective of constant
rank `k`; the union of these closed subschemes over `k` is the chart of pole order `N` of the loop
Grassmannian of `GL_n` (Zhu, §1.1).

The closed subscheme is the instance `Module.Grassmannian.schemeIdealLocus` of the general
construction of closed subschemes of `G(k, M)` cut out by ideals of points: stability is cut out
by the ideal `Module.Grassmannian.stableLocus`, whose formation commutes with base change
(`Module.Grassmannian.stableLocus_map`). It commutes with base change along `Spec R' ⟶ Spec R`,
because the ideal `stableLocus` of a point of the Grassmannian of `R' ⊗[R] M` for the base change
of `t` agrees with that of its image in the Grassmannian of `M` for `t`
(`Module.Grassmannian.stableLocus_baseChangeEquiv`).

The scheme structure is the one of the functor of points, and it is not reduced in general. For
the nilpotent Jordan block `t` on a free module of rank two, with `t e₁ = 0` and `t e₂ = e₁`, the
stable lines over `A` are the lines of `e₁ + a e₂` with `a² = 0`
(`Module.Grassmannian.jordanBlockStableEquiv`), so the closed subscheme of stable lines is
`Spec R[ε]` (`Module.Grassmannian.isIso_jordanBlockStableLocusHom`), which is not reduced when
`R` is nontrivial, and over a field it has the single point of the line of `e₁`.

## Main definitions

* `Module.Grassmannian.schemeStableLocus k t`: the ideal sheaf on `G(k, M)` of the closed
  subscheme of `t`-stable submodules.
* `Module.Grassmannian.schemeStableLocusHomEquiv k t A`: the `t`-stable points of
  `G(k, A ⊗[R] M; A)` are the morphisms from `Spec A` to this closed subscheme over `Spec R`.
* `Module.Grassmannian.jordanBlockStableLocusHom b ht₁ ht₂`: for the nilpotent Jordan block on a
  free module of rank two, the morphism from `Spec R[ε]` to the closed subscheme of stable lines.

## Main results

* `Module.Grassmannian.comap_toSchemeHom_schemeStableLocus`: the inverse image of the closed
  subscheme along the morphism `Spec A ⟶ G(k, M)` classifying a point `N` is the zero scheme of
  `N.stableLocus t`.
* `Module.Grassmannian.schemeStableLocus_le_ker_toSchemeHom_iff`: **the universal property**; the
  morphism classifying `N` factors through the closed subscheme exactly when `N` is stable under
  `t_A`.
* `Module.Grassmannian.isProper_subschemeι_schemeStableLocus_toSpec`: for `M` finite over `R`, the
  closed subscheme is proper over `Spec R`.
* `Module.Grassmannian.comap_baseChangeHom_schemeStableLocus` and
  `Module.Grassmannian.isPullback_baseChangeHom_schemeStableLocus`: **base change**; for an
  `R`-algebra `R'`, the closed subscheme of `G(k, R' ⊗[R] M)` of the submodules stable under the
  base change of `t` is the base change of that of `G(k, M)` along `Spec R' ⟶ Spec R`.
* `Module.Grassmannian.schemeStableLocus_zero`: for `t = 0` the closed subscheme is the whole
  Grassmannian.
* `Module.Grassmannian.isIso_jordanBlockStableLocusHom`: for `M` free of rank two and the nilpotent
  Jordan block `t` (`t e₁ = 0`, `t e₂ = e₁`), the closed subscheme of `t`-stable lines is
  `Spec R[ε]`, by the morphism classifying the line of `e₁ + ε e₂`
  (`Module.Grassmannian.jordanBlockStableLocusHom`).
* `Module.Grassmannian.not_isReduced_subscheme_schemeStableLocus_of_jordanBlock` and
  `Module.Grassmannian.subsingleton_subscheme_schemeStableLocus_of_jordanBlock`: so it is not
  reduced over a nontrivial ring, and over a field it has a single point, the line of `e₁`.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7, for
  closed conditions on the Grassmannian.
* X. Zhu, *An introduction to affine Grassmannians and the geometric Satake equivalence*,
  Lecture notes, §1.1, for the lattice charts as `t`-stable points of a Grassmannian.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Scheme.IdealSheafData

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M] {k : ℕ}

variable (k) in
/-- The ideal sheaf of the **closed subscheme of `t`-stable submodules** in the Grassmannian
scheme `G(k, M)`, for an endomorphism `t` of `M`. A morphism `Spec A ⟶ G(k, M)` over `Spec R`,
classifying a point `N` of `G(k, A ⊗[R] M; A)`, factors through this closed subscheme exactly
when `N` is stable under the base change `t_A` of `t`
(`Module.Grassmannian.schemeStableLocus_le_ker_toSchemeHom_iff`). Over an affine open `U`, its
ideal is `Module.Grassmannian.stableLocus` of the point over `Γ(G(k, M), U)` classifying the
inclusion of `U`. -/
noncomputable def schemeStableLocus (t : Module.End R M) : (scheme R M k).IdealSheafData :=
  schemeIdealLocus (R := R) (M := M) (k := k) (fun N ↦ N.stableLocus t)
    fun f N ↦ stableLocus_map f N t

/-- **The inverse image of the closed subscheme of stable submodules along a point.** For an
`R`-algebra `A` and a point `N` of `G(k, A ⊗[R] M; A)`, the inverse image of the closed subscheme
of `t`-stable submodules along the morphism `Spec A ⟶ G(k, M)` classifying `N` is the zero scheme
of `N.stableLocus t`. -/
theorem comap_toSchemeHom_schemeStableLocus (t : Module.End R M) {A : Type u} [CommRing A]
    [Algebra R A] (N : G(k, A ⊗[R] M; A)) :
    (schemeStableLocus k t).comap (toSchemeHom N) =
      ofIdealTop ((N.stableLocus t).map (Scheme.ΓSpecIso (.of A)).inv.hom) :=
  comap_toSchemeHom_schemeIdealLocus (R := R) (M := M) (k := k) (fun N ↦ N.stableLocus t)
    (fun f N ↦ stableLocus_map f N t) N

/-- **The universal property of the closed subscheme of stable submodules.** For an `R`-algebra
`A`, the morphism `Spec A ⟶ G(k, M)` classifying a point `N` of `G(k, A ⊗[R] M; A)` factors
through the closed subscheme of `t`-stable submodules exactly when `N` is stable under the base
change `t_A` of `t`. -/
theorem schemeStableLocus_le_ker_toSchemeHom_iff (t : Module.End R M) {A : Type u} [CommRing A]
    [Algebra R A] (N : G(k, A ⊗[R] M; A)) :
    schemeStableLocus k t ≤ (toSchemeHom N).ker ↔
      N.toSubmodule ∈ Module.End.invtSubmodule (t.baseChange A) :=
  (schemeIdealLocus_le_ker_toSchemeHom_iff (R := R) (M := M) (k := k)
    (fun N ↦ N.stableLocus t) (fun f N ↦ stableLocus_map f N t) N).trans
    (stableLocus_eq_bot_iff N t)

variable (k) in
/-- **The closed subscheme of stable submodules represents the stable points of the
Grassmannian.** For an `R`-algebra `A`, the points `N` of `G(k, A ⊗[R] M; A)` which are stable
under the base change `t_A` of `t` are in bijection with the morphisms from `Spec A` to the closed
subscheme of `t`-stable submodules over `Spec R`. The bijection composes with the inclusion into
`G(k, M)` to the morphism classifying `N`
(`Module.Grassmannian.schemeStableLocusHomEquiv_apply_comp_subschemeι` and
`Module.Grassmannian.toSchemeHom_schemeStableLocusHomEquiv_symm_apply`). -/
noncomputable def schemeStableLocusHomEquiv (t : Module.End R M) (A : Type u) [CommRing A]
    [Algebra R A] :
    {N : G(k, A ⊗[R] M; A) // N.toSubmodule ∈ Module.End.invtSubmodule (t.baseChange A)} ≃
      {h : Spec (.of A) ⟶ (schemeStableLocus k t).subscheme //
        h ≫ (schemeStableLocus k t).subschemeι ≫ toSpec R M k =
          Spec.map (CommRingCat.ofHom (algebraMap R A))} :=
  (Equiv.subtypeEquivRight fun N ↦ (stableLocus_eq_bot_iff N t).symm).trans
    (schemeIdealLocusHomEquiv (R := R) (M := M) (k := k) (fun N ↦ N.stableLocus t)
      (fun f N ↦ stableLocus_map f N t) A)

/-- The morphism to the closed subscheme of stable submodules corresponding to a stable point `N`,
followed by the inclusion into the Grassmannian scheme, is the morphism classifying `N`. -/
@[reassoc (attr := simp)]
theorem schemeStableLocusHomEquiv_apply_comp_subschemeι (t : Module.End R M) {A : Type u}
    [CommRing A] [Algebra R A]
    (N : {N : G(k, A ⊗[R] M; A) // N.toSubmodule ∈ Module.End.invtSubmodule (t.baseChange A)}) :
    (schemeStableLocusHomEquiv k t A N).val ≫ (schemeStableLocus k t).subschemeι =
      toSchemeHom N.val :=
  schemeIdealLocusHomEquiv_apply_comp_subschemeι (R := R) (M := M) (k := k)
    (fun N ↦ N.stableLocus t) (fun f N ↦ stableLocus_map f N t) _

/-- The stable point corresponding to a morphism `h` to the closed subscheme of stable submodules
is the point classified by `h` followed by the inclusion into the Grassmannian scheme. -/
@[simp]
theorem toSchemeHom_schemeStableLocusHomEquiv_symm_apply (t : Module.End R M) {A : Type u}
    [CommRing A] [Algebra R A]
    (h : {h : Spec (.of A) ⟶ (schemeStableLocus k t).subscheme //
      h ≫ (schemeStableLocus k t).subschemeι ≫ toSpec R M k =
        Spec.map (CommRingCat.ofHom (algebraMap R A))}) :
    toSchemeHom ((schemeStableLocusHomEquiv k t A).symm h).val =
      h.val ≫ (schemeStableLocus k t).subschemeι :=
  toSchemeHom_schemeIdealLocusHomEquiv_symm_apply (R := R) (M := M) (k := k)
    (fun N ↦ N.stableLocus t) (fun f N ↦ stableLocus_map f N t) h

/-- For `M` finite over `R`, the closed subscheme of `t`-stable submodules is proper over
`Spec R`, as a closed subscheme of the proper Grassmannian scheme. -/
instance isProper_subschemeι_schemeStableLocus_toSpec [Module.Finite R M] (t : Module.End R M) :
    IsProper ((schemeStableLocus k t).subschemeι ≫ toSpec R M k) :=
  inferInstance

variable (R M k) in
/-- **Every submodule is stable under `t = 0`.** The closed subscheme of submodules stable under
the zero endomorphism is the whole Grassmannian scheme. -/
@[simp]
theorem schemeStableLocus_zero : schemeStableLocus k (0 : Module.End R M) = ⊥ :=
  le_bot_iff.1 <| idealSheafData_le_of_comap_chartι fun x ↦ by
    rw [schemeStableLocus, comap_chartι_schemeIdealLocus, stableLocus_zero, Ideal.map_bot,
      comap_bot]
    exact (OrderIso.map_bot equivOfIsAffine.toOrderIso.symm).le

end Module.Grassmannian

namespace Module.Grassmannian

section BaseChange

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] {M : Type u} [AddCommGroup M]
  [Module R M] {k : ℕ}

variable (R' k) in
/-- **The closed subscheme of stable submodules is compatible with base change.** For an
endomorphism `t` of `M` and an `R`-algebra `R'`, the inverse image of the closed subscheme of
`t`-stable submodules of `G(k, M)` along `G(k, R' ⊗[R] M) ⟶ G(k, M)` is the closed subscheme of
`G(k, R' ⊗[R] M)` of the submodules stable under the base change of `t` to `R'`. -/
@[simp]
theorem comap_baseChangeHom_schemeStableLocus (t : Module.End R M) :
    (schemeStableLocus k t).comap (baseChangeHom R R' M k) =
      schemeStableLocus k (t.baseChange R') :=
  comap_baseChangeHom_schemeIdealLocus _ (fun f N ↦ stableLocus_map f N t) _
    (fun f N ↦ stableLocus_map f N _) fun N ↦ stableLocus_baseChangeEquiv N t

variable (R' k) in
/-- **Base change of the closed subscheme of stable submodules.** For an endomorphism `t` of `M`
and an `R`-algebra `R'`, the closed subscheme of `G(k, R' ⊗[R] M)` of the submodules stable under
the base change of `t`, as a scheme over `Spec R'`, is the base change along `Spec R' ⟶ Spec R` of
the closed subscheme of `t`-stable submodules of `G(k, M)`, as a scheme over `Spec R`. -/
theorem isPullback_baseChangeHom_schemeStableLocus (t : Module.End R M) :
    IsPullback
      (subschemeMap (schemeStableLocus k (t.baseChange R')) (schemeStableLocus k t)
        (baseChangeHom R R' M k)
        (le_map_iff_comap_le.2 (comap_baseChangeHom_schemeStableLocus R' k t).le))
      ((schemeStableLocus k (t.baseChange R')).subschemeι ≫ toSpec R' (R' ⊗[R] M) k)
      ((schemeStableLocus k t).subschemeι ≫ toSpec R M k)
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
  isPullback_baseChangeHom_schemeIdealLocus _ (fun f N ↦ stableLocus_map f N t) _
    (fun f N ↦ stableLocus_map f N _) fun N ↦ stableLocus_baseChangeEquiv N t

end BaseChange

end Module.Grassmannian

namespace Module.Grassmannian

section JordanBlock

open DualNumber

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
  (b : Basis (Fin 1 ⊕ Fin 1) R M) {t : Module.End R M}
  (ht₁ : t (b (.inl 0)) = 0) (ht₂ : t (b (.inr 0)) = b (.inl 0))

/-- The morphism from `Spec R[ε]` to the closed subscheme of lines stable under the nilpotent
endomorphism `t` with `t e₁ = 0` and `t e₂ = e₁` which classifies the stable line of `e₁ + ε e₂`
over the dual numbers. It is an isomorphism
(`Module.Grassmannian.isIso_jordanBlockStableLocusHom`). -/
noncomputable def jordanBlockStableLocusHom :
    Spec (.of R[ε]) ⟶ (schemeStableLocus 1 t).subscheme :=
  (schemeStableLocusHomEquiv 1 t R[ε]
    ((jordanBlockStableEquiv b ht₁ ht₂ R[ε]).symm ⟨ε, by rw [sq, eps_mul_eps]⟩)).val

/-- `jordanBlockStableLocusHom` followed by the inclusion into `G(1, M)` classifies the line of
`e₁ + ε e₂`. -/
@[reassoc]
theorem jordanBlockStableLocusHom_comp_subschemeι :
    jordanBlockStableLocusHom b ht₁ ht₂ ≫ (schemeStableLocus 1 t).subschemeι =
      toSchemeHom ((jordanBlockStableEquiv b ht₁ ht₂ R[ε]).symm
        ⟨ε, by rw [sq, eps_mul_eps]⟩).val :=
  schemeStableLocusHomEquiv_apply_comp_subschemeι t _

/-- `jordanBlockStableLocusHom` lies over `Spec R`. -/
@[reassoc (attr := simp)]
theorem jordanBlockStableLocusHom_toSpec :
    jordanBlockStableLocusHom b ht₁ ht₂ ≫ (schemeStableLocus 1 t).subschemeι ≫ toSpec R M 1 =
      Spec.map (CommRingCat.ofHom (algebraMap R R[ε])) :=
  (schemeStableLocusHomEquiv 1 t R[ε] _).property

/-- An `R`-algebra map `χ : R[ε] → A` composes with `jordanBlockStableLocusHom` to the morphism
classifying the stable line of `e₁ + χ(ε) e₂`. -/
private theorem specMap_comp_jordanBlockStableLocusHom_eq_iff {A : Type u} [CommRing A]
    [Algebra R A] (χ : R[ε] →ₐ[R] A)
    (N : {N : G(1, A ⊗[R] M; A) // N.toSubmodule ∈ Module.End.invtSubmodule (t.baseChange A)}) :
    Spec.map (CommRingCat.ofHom (χ : R[ε] →+* A)) ≫ jordanBlockStableLocusHom b ht₁ ht₂ =
        (schemeStableLocusHomEquiv 1 t A N).val ↔
      χ ε = (jordanBlockStableEquiv b ht₁ ht₂ A N).val := by
  rw [← cancel_mono (schemeStableLocus 1 t).subschemeι, Category.assoc,
    jordanBlockStableLocusHom_comp_subschemeι, ← toSchemeHom_map,
    map_jordanBlockStableEquiv_symm_apply, schemeStableLocusHomEquiv_apply_comp_subschemeι]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := congrArg (jordanBlockStableEquiv b ht₁ ht₂ A)
      (Subtype.ext (toSchemeHom_injective h) : (jordanBlockStableEquiv b ht₁ ht₂ A).symm
        ⟨χ ε, _⟩ = N)
    rw [Equiv.apply_symm_apply] at this
    exact congrArg Subtype.val this
  · congr 2
    rw [Equiv.symm_apply_eq]
    exact Subtype.ext h

include ht₁ ht₂ in
/-- Every affine point of the closed subscheme of stable lines lifts uniquely along
`jordanBlockStableLocusHom`, over `Spec R`. -/
private theorem existsUnique_comp_jordanBlockStableLocusHom {A : CommRingCat.{u}}
    (a : Spec A ⟶ (schemeStableLocus 1 t).subscheme) :
    ∃! c : Spec A ⟶ Spec (.of R[ε]), c ≫ jordanBlockStableLocusHom b ht₁ ht₂ = a ∧
      c ≫ Spec.map (CommRingCat.ofHom (algebraMap R R[ε])) =
        a ≫ (schemeStableLocus 1 t).subschemeι ≫ toSpec R M 1 := by
  -- make `A` an `R`-algebra through `a`, so that `a` classifies a stable line `N`
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ (schemeStableLocus 1 t).subschemeι ≫ toSpec R M 1)
  let _ : Algebra R A := φ.hom.toAlgebra
  have ha : a ≫ (schemeStableLocus 1 t).subschemeι ≫ toSpec R M 1 =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    rw [← hφ, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
  set N := (schemeStableLocusHomEquiv 1 t A).symm ⟨a, ha⟩
  have hN : (schemeStableLocusHomEquiv 1 t A N).val = a := by
    rw [Equiv.apply_symm_apply]
  set x := jordanBlockStableEquiv b ht₁ ht₂ A N
  -- the lift is `Spec` of the `R`-algebra map `R[ε] → A` sending `ε` to the coordinate `x` of `N`
  let ψ : R[ε] →ₐ[R] A := lift ⟨(Algebra.ofId R A, x.val), by rw [← sq]; exact x.property,
    fun _ ↦ Commute.all _ _⟩
  refine ⟨Spec.map (CommRingCat.ofHom (ψ : R[ε] →+* A)), ⟨?_, ?_⟩, ?_⟩
  · rw [← hN, specMap_comp_jordanBlockStableLocusHom_eq_iff]
    simp [ψ, x]
  · rw [ha, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]
  · rintro c ⟨hc₁, hc₂⟩
    obtain ⟨χ₀, rfl⟩ := Spec.map_surjective c
    -- `χ₀` is a map of `R`-algebras, since `c` lies over `Spec R`
    have hχ₀ : (CommRingCat.ofHom (algebraMap R R[ε])) ≫ χ₀ =
        CommRingCat.ofHom (algebraMap R A) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hc₂, ha]
    let χ : R[ε] →ₐ[R] A :=
      { χ₀.hom with commutes' := fun r ↦ DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hχ₀) r }
    have hχ : CommRingCat.ofHom (χ : R[ε] →+* A) = χ₀ := CommRingCat.ofHom_hom χ₀
    rw [← hχ, ← hN, specMap_comp_jordanBlockStableLocusHom_eq_iff] at hc₁
    have hχψ : χ = ψ := algHom_ext <| by simp [ψ, x, hc₁]
    rw [← hχ, hχψ]

/-- **The stable lines of a nilpotent Jordan block form `Spec R[ε]`.** For the nilpotent
endomorphism `t` of `M` with `t e₁ = 0` and `t e₂ = e₁`, the closed subscheme of `G(1, M)` of
`t`-stable lines is isomorphic over `Spec R` to `Spec R[ε] = Spec R[a]/(a²)`, by the morphism
classifying the line of `e₁ + ε e₂`. -/
instance isIso_jordanBlockStableLocusHom : IsIso (jordanBlockStableLocusHom b ht₁ ht₂) := by
  have : IsPullback (jordanBlockStableLocusHom b ht₁ ht₂)
      (Spec.map (CommRingCat.ofHom (algebraMap R R[ε])))
      ((schemeStableLocus 1 t).subschemeι ≫ toSpec R M 1) (𝟙 _) :=
    Scheme.isPullback_of_forall_spec (by simp) fun A a c h ↦ by
      rw [Category.comp_id] at h
      subst h
      exact existsUnique_comp_jordanBlockStableLocusHom b ht₁ ht₂ a
  exact this.isIso_fst_of_isIso

include ht₁ ht₂ in
/-- **The closed subscheme of stable lines of a nilpotent Jordan block is not reduced** over a
nontrivial ring: it is `Spec R[ε]`, and `ε ≠ 0` is nilpotent. -/
theorem not_isReduced_subscheme_schemeStableLocus_of_jordanBlock [Nontrivial R] :
    ¬IsReduced (schemeStableLocus 1 t).subscheme := by
  intro h
  have := isReduced_of_isOpenImmersion (jordanBlockStableLocusHom b ht₁ ht₂)
  rw [affine_isReduced_iff] at this
  exact DualNumber.not_isReduced (R := R) this

end JordanBlock

open DualNumber in
/-- **Over a field, the closed subscheme of stable lines of a nilpotent Jordan block has a single
point**: it is `Spec K[ε]`, and `K[ε]` is a local ring of dimension zero. -/
theorem subsingleton_subscheme_schemeStableLocus_of_jordanBlock {K : Type u} [Field K] {M : Type u}
    [AddCommGroup M] [Module K M] (b : Basis (Fin 1 ⊕ Fin 1) K M) {t : Module.End K M}
    (ht₁ : t (b (.inl 0)) = 0) (ht₂ : t (b (.inr 0)) = b (.inl 0)) :
    Subsingleton (schemeStableLocus 1 t).subscheme := by
  -- `K[ε]` is artinian, so its spectrum is a single point
  have : Subsingleton (Spec (.of K[ε])) := Ring.KrullDimLE.subsingleton_primeSpectrum K[ε]
  exact (jordanBlockStableLocusHom b ht₁ ht₂).homeomorph.symm.injective.subsingleton

end Module.Grassmannian
