/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.CrossedProduct

/-!
# Clifford operators on multiplicity spaces

For an inertia representation `W`, the canonical Clifford group acts on
`Hom_N(A, W)` by `f ↦ W(t) f U⁻¹`, where `(t,U)` is an implementing pair.
The diagonal normal-subgroup action acts trivially, so this depends only on the
Clifford class. Kernel units act by inverse precomposition.

A section therefore gives semilinear operators for the full commutant `End A`.
Their composition has the inverse factor on the right. These are the operators
used to describe isotypic representations over nonsplitting fields; neither
scalar Schur nor semisimplicity is needed. The right commutant module is Mathlib's
native left module over `(End A)ᵐᵒᵖ` on categorical morphisms.

The construction follows the conjugation formula of
`TauCeti.IsProjectiveInertiaExtension.homAction`, retaining the full commutant
and descending through the canonical Clifford group instead of a scalar factor set.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public section

namespace FDRep

open CategoryTheory MulOpposite TauCeti TauCeti.CliffordExtension

universe u v

variable {k : Type u} {G : Type v} [Group G] {N : Subgroup G} [N.Normal]

section CommRing

variable [CommRing k] (A : FDRep k N) (W : FDRep k (inertia A))

/-- The operator of an inverse implementing pair is the inverse linear equivalence. -/
private theorem implementers_inv_snd (p : implementers A) : (p⁻¹).1.2 = p.1.2.symm := by
  ext x
  simp only [Subgroup.coe_inv, Prod.snd_inv, LinearEquiv.coe_inv]

private noncomputable def implementerMap (p : implementers A)
    (f : A ⟶ (Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).obj W) :
    A ⟶ (Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).obj W where
  hom := FGModuleCat.ofHom ((W.ρ p.1.1).comp (f.hom.hom.hom.comp p.1.2.symm.toLinearMap))
  comm n := by
    apply FGModuleCat.hom_ext
    ext x
    have hU : p.1.2.symm (A.ρ n x) =
        A.ρ (MulAut.conjNormal (p.1.1 : G)⁻¹ n) (p.1.2.symm x) :=
      (mem_implementers_iff A _).mp (p⁻¹).2 n x
    have hf : f.hom.hom.hom
        (A.ρ (MulAut.conjNormal (p.1.1 : G)⁻¹ n) (p.1.2.symm x)) =
        W.ρ (Subgroup.inclusion (le_inertia A) (MulAut.conjNormal (p.1.1 : G)⁻¹ n))
          (f.hom.hom.hom (p.1.2.symm x)) :=
      LinearMap.congr_fun (FDRep.hom_hom_hom_comm f
        (MulAut.conjNormal (p.1.1 : G)⁻¹ n)) (p.1.2.symm x)
    have hn : p.1.1 * Subgroup.inclusion (le_inertia A)
        (MulAut.conjNormal (p.1.1 : G)⁻¹ n) =
        Subgroup.inclusion (le_inertia A) n * p.1.1 :=
      Subtype.ext (by simp [mul_assoc])
    -- Read the restricted action and categorical composition on the underlying vectors.
    change W.ρ p.1.1 (f.hom.hom.hom (p.1.2.symm (A.ρ n x))) =
      W.ρ (Subgroup.inclusion (le_inertia A) n)
        (W.ρ p.1.1 (f.hom.hom.hom (p.1.2.symm x)))
    rw [hU, hf]
    have hmul : W.ρ p.1.1 *
        W.ρ (Subgroup.inclusion (le_inertia A) (MulAut.conjNormal (p.1.1 : G)⁻¹ n)) =
        W.ρ (Subgroup.inclusion (le_inertia A) n) * W.ρ p.1.1 := by
      rw [← map_mul, hn, map_mul]
    exact congrArg (fun l : Module.End k W => l (f.hom.hom.hom (p.1.2.symm x))) hmul

private theorem implementerMap_apply (p : implementers A)
    (f : A ⟶ (Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).obj W) (x : A) :
    (implementerMap A W p f).hom.hom.hom x =
      W.ρ p.1.1 (f.hom.hom.hom (p.1.2.symm x)) := (rfl)

/-- Implementing pairs act on the multiplicity space by conjugating intertwiners. -/
private noncomputable def implementerMultiplicity :
    Representation k (implementers A)
      (A ⟶ (Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).obj W) where
  toFun p :=
    { toFun := implementerMap A W p
      map_add' f g := by
        ext x
        -- Addition of action morphisms is addition of their underlying linear maps.
        change W.ρ p.1.1 (f.hom.hom.hom (p.1.2.symm x) +
          g.hom.hom.hom (p.1.2.symm x)) =
          W.ρ p.1.1 (f.hom.hom.hom (p.1.2.symm x)) +
            W.ρ p.1.1 (g.hom.hom.hom (p.1.2.symm x))
        exact map_add _ _ _
      map_smul' r f := by
        ext x
        -- Scalar multiplication is inherited through the full subcategory.
        change W.ρ p.1.1 (r • f.hom.hom.hom (p.1.2.symm x)) =
          r • W.ρ p.1.1 (f.hom.hom.hom (p.1.2.symm x))
        exact map_smul _ _ _ }
  map_one' := by
    ext f x
    -- Evaluate the linear-map constructor and the identity implementing pair.
    change W.ρ 1 (f.hom.hom.hom ((1 : A ≃ₗ[k] A).symm x)) = f.hom.hom.hom x
    simp only [map_one, FGModuleCat.obj_carrier]
    exact Module.End.one_apply _
  map_mul' p q := by
    ext f x
    -- Multiplication of endomorphisms is composition; unbundle it before evaluation.
    change (implementerMap A W (p * q) f).hom.hom.hom x =
      (implementerMap A W p (implementerMap A W q f)).hom.hom.hom x
    simp only [implementerMap_apply, Subgroup.coe_mul, Prod.fst_mul, Prod.snd_mul,
      ← LinearEquiv.coe_inv, mul_inv_rev, LinearEquiv.mul_apply]
    exact congrArg (fun l : Module.End k W =>
      l (f.hom.hom.hom (q.1.2.symm (p.1.2.symm x)))) (map_mul W.ρ p.1.1 q.1.1)

/-- The action of an implementing pair, evaluated on an underlying vector. -/
@[simp]
private theorem implementerMultiplicity_apply (p : implementers A)
    (f : A ⟶ (Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).obj W) (x : A) :
    (implementerMultiplicity A W p f).hom.hom.hom x =
      W.ρ p.1.1 (f.hom.hom.hom (p.1.2.symm x)) := (rfl)

/-- The diagonal copy of `N` acts trivially on multiplicities. -/
@[simp]
private theorem implementerMultiplicity_diagonal (n : N) :
    implementerMultiplicity A W (diagonal A n) = 1 := by
  ext f x
  have hi : (diagonal A n).1.2.symm = (diagonal A n⁻¹).1.2 := by
    rw [map_inv, implementers_inv_snd]
  have hf : f.hom.hom.hom (A.ρ n⁻¹ x) =
      W.ρ (Subgroup.inclusion (le_inertia A) n⁻¹) (f.hom.hom.hom x) :=
    LinearMap.congr_fun (FDRep.hom_hom_hom_comm f n⁻¹) x
  simp only [implementerMultiplicity_apply, hi, diagonal_snd_apply, hf, diagonal_fst]
  rw [(Subgroup.inclusion (le_inertia A)).map_inv]
  exact Representation.self_inv_apply W.ρ _ _

/-- The Clifford group acts on the multiplicity space of an inertia representation.
Its kernel acts by inverse precomposition, rather than by scalar multiplication. -/
noncomputable def cliffordMultiplicityRepresentation :
    Representation k (Carrier A)
      (A ⟶ (Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).obj W) :=
  QuotientGroup.lift _ (implementerMultiplicity A W) (by
    rintro _ ⟨n, rfl⟩
    exact implementerMultiplicity_diagonal A W n)

/-- A represented Clifford class acts by conjugating the intertwiner. -/
@[simp]
theorem cliffordMultiplicityRepresentation_mk_apply (p : implementers A)
    (f : A ⟶ (Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).obj W)
    (x : A) :
    (cliffordMultiplicityRepresentation A W (QuotientGroup.mk p) f).hom.hom.hom x =
      W.ρ p.1.1 (f.hom.hom.hom (p.1.2.symm x)) := (rfl)

/-- A kernel unit acts on `Hom_N(A,W)` by precomposition with its inverse. -/
@[simp]
theorem cliffordMultiplicityRepresentation_mk_kernelLift (d : (End A)ˣ)
    (f : A ⟶ (Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).obj W) :
    cliffordMultiplicityRepresentation A W (QuotientGroup.mk (kernelLift A d)) f =
      op (↑d⁻¹ : End A) • f := by
  ext x
  have hi : (kernelLift A d).1.2.symm = (kernelLift A d⁻¹).1.2 := by
    rw [map_inv, implementers_inv_snd]
  simp only [cliffordMultiplicityRepresentation_mk_apply, op_smul_apply,
    kernelLift_fst, hi, kernelLift_snd_apply, map_one]
  exact Module.End.one_apply (R := k) (M := W) _

/-- Clifford operators are semilinear for the full commutant action. -/
theorem cliffordMultiplicityRepresentation_smul (c : Carrier A) (d : End A)
    (f : A ⟶ (Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).obj W) :
    cliffordMultiplicityRepresentation A W c (op d • f) =
      op (commutantAction c d) • cliffordMultiplicityRepresentation A W c f := by
  refine QuotientGroup.induction_on c fun p => ?_
  ext x
  simp only [commutantAction_mk, cliffordMultiplicityRepresentation_mk_apply, op_smul_apply]
  rw [implementerConj_apply, LinearEquiv.symm_apply_apply]

/-- Postcomposition with an inertia intertwiner commutes with the Clifford action. -/
theorem cliffordMultiplicityRepresentation_naturality {W' : FDRep k (inertia A)}
    (g : W ⟶ W') (c : Carrier A)
    (f : A ⟶ (Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).obj W) :
    cliffordMultiplicityRepresentation A W c f ≫
        (Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).map g =
      cliffordMultiplicityRepresentation A W' c
        (f ≫ (Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).map g) := by
  refine QuotientGroup.induction_on c fun p => ?_
  ext x
  -- Restriction leaves the underlying linear map of `g` unchanged.
  change g.hom.hom.hom (W.ρ p.1.1 (f.hom.hom.hom (p.1.2.symm x))) =
    W'.ρ p.1.1 (g.hom.hom.hom (f.hom.hom.hom (p.1.2.symm x)))
  exact LinearMap.congr_fun (FDRep.hom_hom_hom_comm g p.1.1) _

end CommRing

section Field

variable [Field k] (A : FDRep k N) (W : FDRep k (inertia A))
  (s : (groupExtension A).Section)

/-- Composing section operators introduces the inverse crossed-system factor on the right.
Equivalently the left coefficient algebra for multiplicities uses the opposite coefficients
and the opposite of the inverse factor. -/
theorem cliffordMultiplicityRepresentation_section_mul (hs : s 1 = 1) (q r : Quotient A)
    (f : A ⟶ (Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).obj W) :
    cliffordMultiplicityRepresentation A W (s q) (cliffordMultiplicityRepresentation A W (s r) f) =
      op (↑((FDRep.cliffordCrossedSystem A s hs).factor q r)⁻¹ : End A) •
        cliffordMultiplicityRepresentation A W (s (q * r)) f := by
  -- Write `s q * s r` as the kernel image of the factor times `s (q * r)`, then act by each part.
  calc cliffordMultiplicityRepresentation A W (s q) (cliffordMultiplicityRepresentation A W (s r) f)
      = cliffordMultiplicityRepresentation A W ((s q : Carrier A) * s r) f := by
        rw [map_mul, Module.End.mul_apply]
    _ = cliffordMultiplicityRepresentation A W
          (inl A ((FDRep.cliffordCrossedSystem A s hs).factor q r) * s (q * r)) f := by
        rw [TauCeti.GroupExtension.section_mul, groupExtension_inl, cliffordCrossedSystem_factor]
    _ = cliffordMultiplicityRepresentation A W
          (QuotientGroup.mk (kernelLift A ((FDRep.cliffordCrossedSystem A s hs).factor q r)))
          (cliffordMultiplicityRepresentation A W (s (q * r)) f) := by
        rw [map_mul, Module.End.mul_apply, inl_apply]
    _ = _ := cliffordMultiplicityRepresentation_mk_kernelLift A W _ _

end Field

end FDRep
