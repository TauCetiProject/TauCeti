/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.StrictHenselization.Local
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import TauCeti.RingTheory.Unramified.Diagonal

/-!
# Maps from étale algebras to the strict henselization

Let `algebra R Ω` be the colimit of the pointed étale neighbourhoods of `(R, Ω)` and
`toTarget : algebra R Ω →ₐ[R] Ω` the map induced by their pointings. For an étale `R`-algebra
`A`, composing with `toTarget` is a bijection from `R`-algebra maps `A → algebra R Ω` to
`R`-algebra maps `A → Ω` (`toTarget_comp_bijective`). Surjectivity holds because a point
`A → Ω` makes `A` itself a pointed neighbourhood, whose stage map lifts the point. Injectivity
holds for every essentially finite type unramified `A`, because the kernel of `toTarget` lies in
the Jacobson radical of the colimit (`toTarget_comp_injective`).

For a local ring `R` and a separable closure `Ω` of its residue field, this is the statement of
Stacks, Tag 04GT, with `S = R`, about the strict henselization. In the form given there
(`existsUnique_algHom_of_etale`), a point of `A` is a prime `𝔮` of `A` with an `R`-embedding
`κ(𝔮) → Ω`, and the map `A → R^{sh}` it determines pulls the maximal ideal back to `𝔮`.

## Main results

* `TauCeti.StrictHenselization.toTarget_comp_injective`: maps from an essentially finite type
  unramified algebra to the colimit are determined by their composites with `toTarget`.
* `TauCeti.StrictHenselization.toTarget_comp_bijective`: for an étale algebra, composition with
  `toTarget` is bijective.
* `TauCeti.StrictHenselization.existsUnique_algHom_of_etale`: the form of Stacks, Tag 04GT, for
  a field `Ω`.

## References

* Stacks Project, Tag 04GT.
-/

public section

open IsLocalRing

universe u w

namespace TauCeti.StrictHenselization

section Pointed

variable (R Ω : Type u) [CommRing R] [CommRing Ω] [Algebra R Ω]

/-- Maps from an essentially finite type unramified `R`-algebra to the colimit of pointed étale
neighbourhoods are determined by their composites with `toTarget`. -/
theorem toTarget_comp_injective (A : Type w) [CommRing A] [Algebra R A]
    [Algebra.EssFiniteType R A] [Algebra.FormallyUnramified R A] :
    Function.Injective ((toTarget R Ω).comp : (A →ₐ[R] algebra R Ω) → A →ₐ[R] Ω) := by
  intro f g h
  apply TauCeti.Algebra.FormallyUnramified.ext_of_quotient_eq R A _
    (ker_toTarget_le_jacobson R Ω)
  ext a
  rw [AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero]
  exact DFunLike.congr_fun h a

/-- Every point of an étale `R`-algebra `A` in the universe of `R` and `Ω` lifts through
`toTarget`: the point makes `A` a pointed neighbourhood, and its stage map is a lift. -/
private theorem exists_toTarget_comp_eq_of_small (A : Type u) [CommRing A] [Algebra R A]
    [Algebra.Etale R A] (point : A →ₐ[R] Ω) :
    ∃ f : A →ₐ[R] algebra R Ω, (toTarget R Ω).comp f = point :=
  ⟨stage R Ω (.mk' A point), (toTarget_comp_stage R Ω _).trans (Neighbourhood.point_mk' A point)⟩

/-- **Étale algebras map to the pointed colimit through their points.** For an étale
`R`-algebra `A`, every `R`-algebra map `A → Ω` lifts uniquely through `toTarget` to an `R`-algebra
map `A → algebra R Ω`. For a local ring `R` and a separable closure `Ω` of its residue field,
`algebra R Ω` is the strict henselization. -/
@[stacks 04GT "S = R, pointed-colimit form"]
theorem toTarget_comp_bijective (A : Type w) [CommRing A] [Algebra R A] [Algebra.Etale R A] :
    Function.Bijective ((toTarget R Ω).comp : (A →ₐ[R] algebra R Ω) → A →ₐ[R] Ω) := by
  refine ⟨toTarget_comp_injective R Ω A, fun point ↦ ?_⟩
  -- Replace `A` by an isomorphic quotient of a polynomial ring, which lives in `Type u`.
  obtain ⟨n, s, hs⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R A)
  let e := Ideal.quotientKerAlgEquivOfSurjective hs
  have : Algebra.Etale R (MvPolynomial (Fin n) R ⧸ RingHom.ker s) := .of_equiv e.symm
  obtain ⟨f, hf⟩ := exists_toTarget_comp_eq_of_small R Ω _ (point.comp e.toAlgHom)
  refine ⟨f.comp e.symm.toAlgHom, ?_⟩
  rw [← AlgHom.comp_assoc, hf, AlgHom.comp_assoc]
  ext a
  simp

end Pointed

section Field

variable (R : Type u) {Ω : Type u} [CommRing R] [Field Ω] [Algebra R Ω]

/-- **Points of étale algebras, Stacks form.** Let `Ω` be a field. For an étale `R`-algebra `A`,
a prime `𝔮` of `A` and an `R`-algebra map `φ : κ(𝔮) → Ω`, there is a unique `R`-algebra map
`f : A → algebra R Ω` inducing `φ` on residue fields, and it pulls the maximal ideal of
`algebra R Ω` back to `𝔮`. For a local ring `R` and a separable closure `Ω` of its residue
field, `algebra R Ω` is the strict henselization, and a prime `𝔮` admitting such a `φ` lies over
the maximal ideal of `R`. -/
@[stacks 04GT "S = R"]
theorem existsUnique_algHom_of_etale (A : Type w) [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (q : Ideal A) [q.IsPrime] (φ : q.ResidueField →ₐ[R] Ω) :
    ∃! f : A →ₐ[R] algebra R Ω, (maximalIdeal (algebra R Ω)).comap f = q ∧
      ∀ a : A, toTarget R Ω (f a) = φ (algebraMap A q.ResidueField a) := by
  let point := φ.comp (IsScalarTower.toAlgHom R A q.ResidueField)
  obtain ⟨f, hf⟩ := (toTarget_comp_bijective R Ω A).2 point
  refine ⟨f, ⟨?_, fun a ↦ DFunLike.congr_fun hf a⟩, fun g hg ↦
    (toTarget_comp_bijective R Ω A).1 (hf ▸ AlgHom.ext hg.2)⟩
  ext a
  rw [← ker_toTarget_eq_maximalIdeal, Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, ← AlgHom.comp_apply, hf, AlgHom.comp_apply, map_eq_zero,
    IsScalarTower.coe_toAlgHom', Ideal.algebraMap_residueField_eq_zero]

end Field

end TauCeti.StrictHenselization
