/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Basic
public import TauCeti.GroupTheory.GroupExtension.FactorSetOfSection

/-!
# The Clifford group's action on the commutant

The canonical Clifford group acts by algebra automorphisms on the actual equivariant
endomorphism algebra `CategoryTheory.End A`. An implementing pair `(t, U)` acts by
`f ↦ U f U⁻¹`. The diagonal copy of the given normal-subgroup action acts trivially,
so conjugation descends to the Clifford quotient. Its kernel units act by inner
conjugation, compatibly with the native group extension's conjugation action.

This algebra action is the input to the noncommutative crossed-system description of
Clifford theory: choosing a section gives automorphisms of the commutant, rather than
an action on scalar coefficients. No scalar-Schur or semisimplicity hypothesis is used.

## References

G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985).
-/

public section

namespace TauCeti.CliffordExtension

open CategoryTheory

universe u v

variable {k : Type u} {G : Type v} [CommRing k] [Group G]
  {N : Subgroup G} [N.Normal] {A : FDRep k N}

private def conjugateEnd (p : implementers A) (f : End A) : End A :=
  End.of
    { hom := FGModuleCat.ofHom (p.1.2.conj f.asHom.hom.hom.hom)
      comm n := by
        apply FGModuleCat.hom_ext
        ext x
        -- Unbundle the full-subcategory morphisms before using the operator equations.
        change p.1.2 (f.asHom.hom.hom.hom (p.1.2.symm (A.ρ n x))) =
          A.ρ n (p.1.2 (f.asHom.hom.hom.hom (p.1.2.symm x)))
        have hU : p.1.2.symm (A.ρ n x) =
            A.ρ (MulAut.conjNormal (p.1.1 : G)⁻¹ n) (p.1.2.symm x) :=
          (mem_implementers_iff A _).mp (p⁻¹).2 n x
        have hf := LinearMap.congr_fun (FDRep.hom_hom_hom_comm f.asHom
          (MulAut.conjNormal (p.1.1 : G)⁻¹ n)) (p.1.2.symm x)
        dsimp only [LinearMap.comp_apply] at hf
        simpa using (congrArg p.1.2 ((congrArg f.asHom.hom.hom.hom hU).trans hf)).trans
          ((mem_implementers_iff A _).mp p.2
            (MulAut.conjNormal (p.1.1 : G)⁻¹ n) (f.asHom.hom.hom.hom (p.1.2.symm x))) }

private theorem conjugateEnd_apply (p : implementers A) (f : End A) (x : A) :
    (conjugateEnd p f).asHom.hom.hom.hom x =
      p.1.2 (f.asHom.hom.hom.hom (p.1.2.symm x)) := (rfl)

/-- An implementing pair conjugates the equivariant endomorphism algebra. -/
noncomputable def implementerConj (p : implementers A) : End A ≃ₐ[k] End A where
  toFun := conjugateEnd p
  invFun := conjugateEnd p⁻¹
  left_inv f := by
    apply End.ext
    ext x
    have hi : (p⁻¹).1.2 = p.1.2.symm := rfl
    simp only [conjugateEnd_apply, hi, LinearEquiv.symm_symm,
      LinearEquiv.symm_apply_apply]
  right_inv f := by
    apply End.ext
    ext x
    have hi : (p⁻¹).1.2 = p.1.2.symm := rfl
    simp only [conjugateEnd_apply, hi, LinearEquiv.symm_symm,
      LinearEquiv.apply_symm_apply]
  map_mul' f g := by
    apply End.ext
    ext x
    simp [conjugateEnd_apply]
  map_add' f g := by
    apply End.ext
    ext x
    -- Unbundle the additive morphisms of the full subcategory to linear maps.
    change p.1.2 (f.asHom.hom.hom.hom (p.1.2.symm x) +
      g.asHom.hom.hom.hom (p.1.2.symm x)) = _
    exact p.1.2.map_add _ _
  commutes' r := by
    apply End.ext
    ext x
    rw [Algebra.algebraMap_eq_smul_one]
    -- Scalar multiplication and identity morphisms reduce through the full subcategory.
    change p.1.2 (r • p.1.2.symm x) = r • x
    simp

/-- The conjugation formula on underlying vectors. -/
@[simp]
theorem implementerConj_apply (p : implementers A) (f : End A) (x : A) :
    (implementerConj p f).asHom.hom.hom.hom x =
      p.1.2 (f.asHom.hom.hom.hom (p.1.2.symm x)) := (rfl)

/-- Conjugation is multiplicative in the implementing pair. -/
@[simp]
theorem implementerConj_mul (p q : implementers A) :
    implementerConj (p * q) = implementerConj p * implementerConj q := by
  apply AlgEquiv.ext
  intro f
  apply End.ext
  ext x
  simp [← LinearEquiv.coe_inv]

@[simp]
theorem implementerConj_one : implementerConj (1 : implementers A) = 1 := by
  apply AlgEquiv.ext
  intro f
  apply End.ext
  ext x
  simp [← LinearEquiv.coe_inv]

/-- The given normal-subgroup action commutes with every equivariant endomorphism. -/
@[simp]
theorem implementerConj_diagonal (n : N) : implementerConj (diagonal A n) = 1 := by
  apply AlgEquiv.ext
  intro f
  apply End.ext
  ext x
  have hf := LinearMap.congr_fun (FDRep.hom_hom_hom_comm f.asHom n)
    ((diagonal A n).1.2.symm x)
  dsimp only [LinearMap.comp_apply] at hf
  rw [← diagonal_snd_apply] at hf
  simpa using hf.symm

/-- The canonical Clifford group acts on the full equivariant endomorphism algebra. -/
noncomputable def commutantAction : Carrier A →* (End A ≃ₐ[k] End A) :=
  QuotientGroup.lift _
    { toFun := implementerConj
      map_one' := implementerConj_one
      map_mul' := implementerConj_mul }
    (by
      rintro _ ⟨n, rfl⟩
      exact implementerConj_diagonal n)

/-- On a represented Clifford class, the action is conjugation by its implementing operator. -/
@[simp]
theorem commutantAction_mk (p : implementers A) :
    commutantAction (QuotientGroup.mk p : Carrier A) = implementerConj p := (rfl)

/-- Kernel units act on the commutant by inner conjugation. -/
@[simp]
theorem implementerConj_kernelLift (d : (End A)ˣ) (f : End A) :
    implementerConj (kernelLift A d) f = (d : End A) * f * (↑d⁻¹ : End A) := by
  apply End.ext
  ext x
  have hi : (kernelLift A d).1.2.symm = (kernelLift A d⁻¹).1.2 := by
    rw [map_inv]
    rfl
  simp only [implementerConj_apply, hi, kernelLift_snd_apply]
  rfl

private theorem kernelLift_map_implementerConj (p : implementers A) (d : (End A)ˣ) :
    kernelLift A (Units.map (implementerConj p).toMonoidHom d) =
      p * kernelLift A d * p⁻¹ := by
  apply Subtype.ext
  apply Prod.ext
  · simp
  · ext x
    simp [kernelLift_snd_apply, ← LinearEquiv.coe_inv]

/-- The algebra action on units agrees with conjugation inside the Clifford group. -/
theorem inl_map_commutantAction (c : Carrier A) (d : (End A)ˣ) :
    inl A (Units.map (commutantAction c).toMonoidHom d) = c * inl A d * c⁻¹ := by
  refine QuotientGroup.induction_on c fun p => ?_
  simp only [commutantAction_mk, inl_apply, kernelLift_map_implementerConj,
    QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rfl

section Field

variable {K : Type u} [Field K]

/-- On units, the commutant action recovers the native extension's conjugation action. -/
theorem commutantAction_units {A : FDRep K N} (c : Carrier A) (d : (End A)ˣ) :
    Units.map (commutantAction c).toMonoidHom d = (groupExtension A).conjAct c d := by
  apply inl_injective A
  rw [inl_map_commutantAction, ← groupExtension_inl, GroupExtension.inl_conjAct_comm]

/-- A section's commutant automorphisms satisfy the inner-twisted multiplication law.
The twisting unit is the factor of the actual canonical Clifford extension. -/
theorem commutantAction_section_mul {A : FDRep K N} (s : (groupExtension A).Section)
    (q r : Quotient A) (f : End A) :
    commutantAction (s q) (commutantAction (s r) f) =
      (↑(TauCeti.GroupExtension.factorSetFun s (q, r)) : End A) *
        commutantAction (s (q * r)) f *
          (↑((TauCeti.GroupExtension.factorSetFun s (q, r))⁻¹) : End A) := by
  rw [← AlgEquiv.mul_apply, ← map_mul, TauCeti.GroupExtension.section_mul]
  rw [map_mul, AlgEquiv.mul_apply, groupExtension_inl]
  simp

end Field

end TauCeti.CliffordExtension
