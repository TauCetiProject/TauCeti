/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.RingTheory.Etale.IndEtale
public import TauCeti.RingTheory.Henselian.Section
import TauCeti.Algebra.Category.CommAlgCat.SmallFilteredColimit

/-!
# Sections of ind-étale algebras over Henselian pairs and Henselian local rings

Over a Henselian pair `(S, J)`, an `R`-algebra map from an étale `R`-algebra to `S ⧸ J` lifts
uniquely to `S` (`TauCeti.HenselianRing.comp_bijective_of_algebra`). Since an ind-étale algebra
is a filtered colimit of étale algebras, and maps out of a colimit into a target in any universe
are compatible families of maps out of its stages (`TauCeti.SmallFilteredAlgebraColimit`), the
unique lifts on the stages assemble into a unique lift on the colimit. Reduction modulo `J` is
therefore a bijection on `R`-algebra maps out of an ind-étale `R`-algebra.

Specialising to a Henselian local `R`-algebra `S` and a surjective `R`-algebra map `χ : S → L`
onto a field `L`, the kernel of `χ` is the maximal ideal of `S`, so post-composition with `χ` is a
bijection from `R`-algebra maps `A → S` to `R`-algebra maps `A → L` (Stacks, Lemma 10.154.6
(08HR)). Taking `χ` to be the residue map `S → κ(S)` recovers unique lifting of residue-field
points out of any ind-étale algebra.

## Main results

* `TauCeti.HenselianRing.comp_bijective_of_indEtale`: for a Henselian pair `(S, J)` with `S` an
  `R`-algebra and an ind-étale `R`-algebra `A`, reduction modulo `J` is a bijection from
  `R`-algebra maps `A → S` to `R`-algebra maps `A → S ⧸ J`.
* `TauCeti.HenselianLocalRing.comp_bijective_of_surjective`: for a Henselian local `R`-algebra `S`,
  a surjective `R`-algebra map `χ : S → L` to a field, and an ind-étale `R`-algebra `A`,
  post-composition with `χ` is a bijection `(A →ₐ[R] S) → (A →ₐ[R] L)`.
* `TauCeti.HenselianLocalRing.comp_bijective_of_indEtale`: the case `L = κ(S)` of residue-field
  points.

## References

* [Stacks Project, Lemma 15.11.6 (09XI)](https://stacks.math.columbia.edu/tag/09XI), the étale
  case for Henselian pairs.
* [Stacks Project, Lemma 10.154.6 (08HR)](https://stacks.math.columbia.edu/tag/08HR), maps out of
  ind-étale algebras into Henselian local rings.
* D. Clausen, A. Mathew, M. Morrow, *K-theory and topological cyclic homology of henselian
  pairs*, J. Amer. Math. Soc. 34 (2021), Remark 3.19.
-/

public section

open CategoryTheory Limits IsLocalRing

universe u v w

namespace TauCeti

namespace HenselianRing

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] (J : Ideal S)
  [HenselianRing S J] {A : Type u} [CommRing A] [Algebra R A] [Algebra.IndEtale R A]

/-- **Sections of ind-étale algebras over a Henselian pair.** For a Henselian pair `(S, J)` with
`S` an `R`-algebra in any universe and an ind-étale `R`-algebra `A`, reduction modulo `J` is a
bijection from `R`-algebra maps `A → S` to `R`-algebra maps `A → S ⧸ J`. The étale case is
`comp_bijective_of_algebra`. -/
theorem comp_bijective_of_indEtale :
    Function.Bijective ((Ideal.Quotient.mkₐ R J).comp : (A →ₐ[R] S) → A →ₐ[R] S ⧸ J) := by
  obtain ⟨ι, _, _, pres, hD⟩ := Algebra.IndEtale.ind_etale (R := R) (S := A)
  -- On each étale stage `Dᵢ` of the presentation, reduction modulo `J` is bijective.
  have hst (i : ι) :
      Function.Bijective ((Ideal.Quotient.mkₐ R J).comp : (pres.diag.obj i →ₐ[R] S) → _) :=
    have := hD i
    comp_bijective_of_algebra J
  refine ⟨fun f g hfg ↦
    SmallFilteredAlgebraColimit.hom_ext_of_isColimit pres.isColimit fun i ↦ (hst i).1 ?_,
    fun ψ ↦ ?_⟩
  · simp only [← AlgHom.comp_assoc, hfg]
  -- Lift `ψ` on each stage, and glue the lifts, which are compatible by uniqueness.
  choose φ hφ using fun i ↦ (hst i).2 (ψ.comp (pres.ι.app i).hom)
  have hcompat {i j : ι} (u : i ⟶ j) : (φ j).comp (pres.diag.map u).hom = φ i :=
    (hst i).1 <| by
      rw [← AlgHom.comp_assoc, hφ, hφ, AlgHom.comp_assoc, ← CommAlgCat.hom_comp, pres.w]
  refine ⟨SmallFilteredAlgebraColimit.descOfCompatibleOfIsColimit pres.isColimit φ hcompat,
    SmallFilteredAlgebraColimit.hom_ext_of_isColimit pres.isColimit fun i ↦ ?_⟩
  rw [AlgHom.comp_assoc, SmallFilteredAlgebraColimit.descOfCompatibleOfIsColimit_comp_ι, hφ]

end HenselianRing

namespace HenselianLocalRing

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Algebra.IndEtale R A]
  {S : Type v} [CommRing S] [Algebra R S] [HenselianLocalRing S]

/-- **Maps out of an ind-étale algebra into a Henselian local ring.** For an ind-étale `R`-algebra
`A`, a Henselian local `R`-algebra `S`, and a surjective `R`-algebra map `χ : S → L` onto a field
`L`, post-composition with `χ` is a bijection from `R`-algebra maps `A → S` to `R`-algebra maps
`A → L`. -/
@[stacks 08HR "bijection on algebra maps out of an ind-étale algebra"]
theorem comp_bijective_of_surjective {L : Type w} [Field L] [Algebra R L] (χ : S →ₐ[R] L)
    (hχ : Function.Surjective χ) :
    Function.Bijective (χ.comp : (A →ₐ[R] S) → A →ₐ[R] L) := by
  -- The kernel of `χ` is the maximal ideal of `S`, so `S ⧸ ker χ ≃ₐ[R] L` reduces this to
  -- `HenselianRing.comp_bijective_of_indEtale`.
  have hker : RingHom.ker χ = maximalIdeal S := ker_eq_maximalIdeal χ.toRingHom hχ
  have : HenselianRing S (RingHom.ker χ) := hker.symm ▸ inferInstance
  let e : (S ⧸ RingHom.ker χ) ≃ₐ[R] L := Ideal.quotientKerAlgEquivOfSurjective hχ
  have hcomp : (χ.comp : (A →ₐ[R] S) → A →ₐ[R] L) =
      (e.toAlgHom.comp : (A →ₐ[R] S ⧸ RingHom.ker χ) → A →ₐ[R] L) ∘
        (Ideal.Quotient.mkₐ R (RingHom.ker χ)).comp := by
    ext f a
    exact (Ideal.quotientKerAlgEquivOfSurjective_mk hχ (f a)).symm
  rw [hcomp]
  refine Function.Bijective.comp ⟨fun g₁ g₂ hg ↦ ?_, fun ψ ↦ ⟨e.symm.toAlgHom.comp ψ, ?_⟩⟩
    (HenselianRing.comp_bijective_of_indEtale (RingHom.ker χ))
  · ext a
    exact e.injective (DFunLike.congr_fun hg a)
  · ext a
    exact e.apply_symm_apply (ψ a)

/-- For an ind-étale `R`-algebra `A` and a Henselian local `R`-algebra `S`, reduction modulo the
maximal ideal of `S` is a bijection from `R`-algebra maps `A → S` to `R`-algebra maps
`A → κ(S)`. -/
theorem comp_bijective_of_indEtale :
    Function.Bijective
      ((IsScalarTower.toAlgHom R S (ResidueField S)).comp :
        (A →ₐ[R] S) → A →ₐ[R] ResidueField S) :=
  comp_bijective_of_surjective (IsScalarTower.toAlgHom R S (ResidueField S)) residue_surjective

end HenselianLocalRing

end TauCeti
