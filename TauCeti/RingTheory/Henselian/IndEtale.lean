/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.IndEtale
public import TauCeti.RingTheory.Henselian.Section

/-!
# Sections of ind-étale algebras over a Henselian pair

Over a Henselian pair `(S, J)`, an `R`-algebra map from an étale `R`-algebra to `S ⧸ J` lifts
uniquely to `S` (`TauCeti.HenselianRing.comp_bijective_of_algebra`). Since an ind-étale algebra
is a filtered colimit of étale algebras, and maps out of a colimit are compatible families of
maps out of its stages, the unique lifts on the stages assemble into a unique lift on the
colimit. So reduction modulo `J` is also a bijection on `R`-algebra maps out of an ind-étale
`R`-algebra.

This is the lifting property behind the recognition of the henselization of a pair as the
ind-étale algebra which is Henselian and has the same closed fibre.

## Main results

* `TauCeti.HenselianRing.comp_bijective_of_indEtale`: for a Henselian pair `(S, J)` with `S` an
  `R`-algebra and an ind-étale `R`-algebra `A`, reduction modulo `J` is a bijection from
  `R`-algebra maps `A → S` to `R`-algebra maps `A → S ⧸ J`.

## References

* [Stacks Project, Lemma 15.11.6 (09XI)](https://stacks.math.columbia.edu/tag/09XI), the étale
  case.
* D. Clausen, A. Mathew, M. Morrow, *K-theory and topological cyclic homology of henselian
  pairs*, J. Amer. Math. Soc. 34 (2021), Remark 3.19.
-/

public section

open CategoryTheory Limits

universe u

namespace TauCeti.HenselianRing

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] (J : Ideal S)
  [HenselianRing S J] {A : Type u} [CommRing A] [Algebra R A] [Algebra.IndEtale R A]

/-- **Sections of ind-étale algebras over a Henselian pair.** For a Henselian pair `(S, J)` with
`S` an `R`-algebra and an ind-étale `R`-algebra `A`, reduction modulo `J` is a bijection from
`R`-algebra maps `A → S` to `R`-algebra maps `A → S ⧸ J`. The étale case is
`comp_bijective_of_algebra`. -/
theorem comp_bijective_of_indEtale :
    Function.Bijective ((Ideal.Quotient.mkₐ R J).comp : (A →ₐ[R] S) → A →ₐ[R] S ⧸ J) := by
  obtain ⟨ι, _, _, pres, hD⟩ := Algebra.IndEtale.ind_etale (R := R) (S := A)
  -- On each étale stage `Dᵢ` of the presentation, reduction modulo `J` is bijective.
  have hst (i : ι) :
      Function.Bijective ((Ideal.Quotient.mkₐ R J).comp : (pres.diag.obj i →ₐ[R] S) → _) :=
    have := hD i
    comp_bijective_of_algebra J
  -- Two maps out of `A` agree once they agree on every stage.
  have hext {T : Type u} [CommRing T] [Algebra R T] {f g : A →ₐ[R] T}
      (h : ∀ i, f.comp (pres.ι.app i).hom = g.comp (pres.ι.app i).hom) : f = g := by
    have : (CommAlgCat.ofHom f : CommAlgCat.of R A ⟶ CommAlgCat.of R T) = CommAlgCat.ofHom g :=
      pres.isColimit.hom_ext fun i ↦ by ext1; exact h i
    simpa using congrArg CommAlgCat.Hom.hom this
  refine ⟨fun f g hfg ↦ hext fun i ↦ (hst i).1 ?_, fun ψ ↦ ?_⟩
  · simp only [← AlgHom.comp_assoc, hfg]
  -- Lift `ψ` on each stage, and glue the lifts, which are compatible by uniqueness.
  choose φ hφ using fun i ↦ (hst i).2 (ψ.comp (pres.ι.app i).hom)
  let c : Cocone pres.diag :=
    { pt := CommAlgCat.of R S
      ι :=
        { app i := CommAlgCat.ofHom (φ i)
          naturality {i j} f := by
            ext1
            refine (hst i).1 ?_
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
              CommAlgCat.hom_comp, CommAlgCat.hom_ofHom, ← AlgHom.comp_assoc, hφ]
            rw [AlgHom.comp_assoc, ← CommAlgCat.hom_comp, pres.w] } }
  refine ⟨(pres.isColimit.desc c).hom, hext fun i ↦ ?_⟩
  rw [AlgHom.comp_assoc, ← CommAlgCat.hom_comp, pres.isColimit.fac c i, ← hφ i]
  simp only [c, CommAlgCat.hom_ofHom]

end TauCeti.HenselianRing
