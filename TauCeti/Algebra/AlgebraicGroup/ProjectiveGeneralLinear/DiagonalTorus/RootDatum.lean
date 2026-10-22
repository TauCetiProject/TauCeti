/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.RootSubgroup.Torus
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.RootDatum.Basic

/-!
# The adjoint type-A datum on the projective diagonal torus

The normalized diagonal torus of `PGL_{r+1}` has character lattice
`ULift (Fin r) →₀ ℤ` and dual cocharacter lattice `ULift (Fin r) → ℤ`.
Its root indexed by `(a,b)` is `ε_a - ε_b`, with `ε_r = 0`. Its coroot
is the class of `e_a - e_b` modulo scalar cocharacters, represented by
subtracting its last coordinate. These vectors form a reduced root datum,
and the roots generate the entire character lattice.

The construction projects the roots and coroots of
`TauCeti.SplitTorus.coordinateRootDatum`, reusing its reflection identities.
The root characters are identified with the characters in the conjugation
formula for the elementary projective root subgroups. Identification with all
nonzero weights of the adjoint representation is a further assertion.

## References

* The API layout and root-character identification follow
  `TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalTorus.RootDatum`.
* J. S. Milne, *Algebraic Groups* (2017), §21.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §§26–27.
-/

public section

namespace TauCeti.ProjectiveGeneralLinear

open SplitTorus WithConv

universe u v

noncomputable section

variable {r : ℕ}

private def rootProjection (r : ℕ) :
    (Fin (r + 1) →₀ ℤ) →ₗ[ℤ] (ULift.{u} (Fin r) →₀ ℤ) :=
  Finsupp.linearCombination ℤ
    (Fin.lastCases 0 (fun i ↦ Finsupp.single (ULift.up i) 1))

private def corootProjection (r : ℕ) :
    (Fin (r + 1) → ℤ) →ₗ[ℤ] (ULift.{u} (Fin r) → ℤ) where
  toFun y i := y i.down.castSucc - y (Fin.last r)
  map_add' y z := by ext i; simp; ring
  map_smul' c y := by ext i; simp [mul_sub]

private lemma corootProjection_apply (y : Fin (r + 1) → ℤ) (i : ULift.{u} (Fin r)) :
    corootProjection r y i = y i.down.castSucc - y (Fin.last r) := (rfl)

private lemma projected_single_pairing (a : Fin (r + 1)) (y : Fin (r + 1) → ℤ) :
    dotPairing (rootProjection.{u} r (Finsupp.single a 1)) (corootProjection r y) =
      y a - y (Fin.last r) := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) a
  · simp [rootProjection]
  · simp [rootProjection, dotPairing_apply, corootProjection_apply]

private lemma projected_root_pairing (a b : Fin (r + 1)) (y : Fin (r + 1) → ℤ) :
    dotPairing (rootProjection.{u} r (coordinateRoot a b)) (corootProjection r y) =
      y a - y b := by
  simp only [coordinateRoot_def, map_sub, LinearMap.sub_apply, projected_single_pairing]
  ring

private lemma projected_pairing (p q : CoordinateRootIndex (Fin (r + 1))) :
    dotPairing (rootProjection.{u} r (coordinateRoot p.1.1 p.1.2))
        (corootProjection r (coordinateCoroot q.1.1 q.1.2)) =
      (coordinateRootDatum (Fin (r + 1))).pairing p q := by
  rw [projected_root_pairing, coordinateRootDatum_pairing_apply]
  simp only [coordinateCoroot_apply, eq_comm]

private lemma projected_root_injective : Function.Injective
    (fun p : CoordinateRootIndex (Fin (r + 1)) ↦
      rootProjection.{u} r (coordinateRoot p.1.1 p.1.2)) := by
  intro p q h
  dsimp only at h
  have ht := projected_pairing.{u} q p
  rw [← h, projected_pairing, RootPairing.pairing_same] at ht
  apply ((coordinateRootDatum (Fin (r + 1))).pairing_two_two_iff p q).mp
  exact ⟨(coordinateRootDatum_pairing_comm p q).trans ht.symm, ht.symm⟩

private lemma projected_coroot_injective : Function.Injective
    (fun p : CoordinateRootIndex (Fin (r + 1)) ↦
      corootProjection.{u} r (coordinateCoroot p.1.1 p.1.2)) := by
  intro p q h
  dsimp only at h
  have ht := projected_pairing.{u} p q
  rw [← h, projected_pairing, RootPairing.pairing_same] at ht
  apply ((coordinateRootDatum (Fin (r + 1))).pairing_two_two_iff p q).mp
  exact ⟨ht.symm, (coordinateRootDatum_pairing_comm q p).trans ht.symm⟩

/-- The reduced adjoint type-`A_r` datum on the character and cocharacter lattices of
the normalized projective diagonal torus, indexed by distinct matrix indices. -/
def diagonalRootDatum (r : ℕ) :
    RootDatum (CoordinateRootIndex (Fin (r + 1)))
      (ULift.{u} (Fin r) →₀ ℤ) (ULift.{u} (Fin r) → ℤ) where
  toLinearMap := dotPairing
  root := ⟨_, projected_root_injective⟩
  coroot := ⟨_, projected_coroot_injective⟩
  root_coroot_two p := by
    simpa only [Function.Embedding.coeFn_mk, projected_pairing] using
      (coordinateRootDatum (Fin (r + 1))).pairing_same p
  reflectionPerm := (coordinateRootDatum (Fin (r + 1))).reflectionPerm
  reflectionPerm_root p q := by
    have h := congrArg (rootProjection.{u} r)
      ((coordinateRootDatum (Fin (r + 1))).reflectionPerm_root p q)
    rw [map_sub, map_smul, RootPairing.root_coroot_eq_pairing] at h
    simpa only [coordinateRootDatum_root, Function.Embedding.coeFn_mk,
      projected_pairing] using h
  reflectionPerm_coroot p q := by
    have h := congrArg (corootProjection.{u} r)
      ((coordinateRootDatum (Fin (r + 1))).reflectionPerm_coroot p q)
    rw [map_sub, map_smul, RootPairing.root_coroot_eq_pairing] at h
    simpa only [coordinateRootDatum_coroot, Function.Embedding.coeFn_mk,
      projected_pairing] using h

/-- The pairing is the perfect split-torus dot pairing. -/
@[simp] theorem diagonalRootDatum_toLinearMap (r : ℕ) :
    (diagonalRootDatum.{u} r).toLinearMap = dotPairing := (rfl)

private lemma rootProjection_single_apply (a : Fin (r + 1)) (i : ULift.{u} (Fin r)) :
    rootProjection r (Finsupp.single a 1) i = if a = i.down.castSucc then 1 else 0 := by
  refine Fin.lastCases ?_ (fun k ↦ ?_) a
  all_goals simp [rootProjection, Finsupp.single_apply, ← ULift.down_inj, eq_comm]

/-- The roots are the matrix-unit weights of the normalized diagonal torus. -/
@[simp] theorem diagonalRootDatum_root_apply (p : CoordinateRootIndex (Fin (r + 1)))
    (i : ULift.{u} (Fin r)) :
    (diagonalRootDatum.{u} r).root p i =
      diagonalTorusWeight r (finProdFinEquiv p.1) i := by
  simp only [diagonalRootDatum, Function.Embedding.coeFn_mk, coordinateRoot_def,
    map_sub, Finsupp.sub_apply, rootProjection_single_apply, diagonalTorusWeight_apply,
    Equiv.symm_apply_apply]

/-- A coroot is represented modulo scalars by subtracting its last coordinate. -/
@[simp] theorem diagonalRootDatum_coroot_apply (p : CoordinateRootIndex (Fin (r + 1)))
    (i : ULift.{u} (Fin r)) :
    (diagonalRootDatum.{u} r).coroot p i =
      ((if p.1.1 = i.down.castSucc then 1 else 0) -
        (if p.1.2 = i.down.castSucc then 1 else 0)) -
      ((if p.1.1 = Fin.last r then 1 else 0) -
        (if p.1.2 = Fin.last r then 1 else 0)) := by
  simp only [diagonalRootDatum, Function.Embedding.coeFn_mk, corootProjection_apply,
    coordinateCoroot_apply, eq_comm]

/-- The Cartan integers are the usual coordinate-difference pairings of type A. -/
@[simp] theorem diagonalRootDatum_pairing_apply (p q : CoordinateRootIndex (Fin (r + 1))) :
    (diagonalRootDatum.{u} r).pairing p q =
      (if p.1.1 = q.1.1 then 1 else 0) - (if p.1.1 = q.1.2 then 1 else 0) -
        ((if p.1.2 = q.1.1 then 1 else 0) - (if p.1.2 = q.1.2 then 1 else 0)) := by
  have h : (diagonalRootDatum.{u} r).pairing p q =
      (coordinateRootDatum (Fin (r + 1))).pairing p q := projected_pairing p q
  -- The coordinate formula uses classical decidability, whereas this statement uses `Fin`'s.
  exact h.trans (by convert coordinateRootDatum_pairing_apply p q)

/-- Reflections transpose both matrix indices. -/
@[simp] theorem diagonalRootDatum_reflectionPerm (p q : CoordinateRootIndex (Fin (r + 1))) :
    (diagonalRootDatum.{u} r).reflectionPerm p q =
      coordinatePermRootIndex (Equiv.swap p.1.1 p.1.2) q :=
  coordinateRootDatum_reflectionPerm p q

/-- The projective diagonal datum is reduced. -/
instance isReduced_diagonalRootDatum (r : ℕ) : (diagonalRootDatum.{u} r).IsReduced := by
  apply RootPairing.isReduced_of_pairing_comm
  intro p q
  simp only [diagonalRootDatum_pairing_apply, eq_comm]
  ring

/-- The root `ε_i - ε_r` is the corresponding basis character in normalized coordinates. -/
theorem diagonalRootDatum_root_castSucc_last (i : ULift.{u} (Fin r)) :
    (diagonalRootDatum.{u} r).root
        ⟨(i.down.castSucc, Fin.last r), (Fin.castSucc_lt_last i.down).ne⟩ =
      Finsupp.single i 1 := by
  ext j
  simp [diagonalRootDatum_root_apply, diagonalTorusWeight_apply,
    Finsupp.single_apply, eq_comm]

/-- The roots span the full character lattice, so this is the adjoint root datum. -/
theorem rootSpan_diagonalRootDatum_eq_top (r : ℕ) :
    (diagonalRootDatum.{u} r).rootSpan ℤ = ⊤ := by
  rw [RootPairing.rootSpan, eq_top_iff,
    ← (Finsupp.basisSingleOne : Module.Basis (ULift.{u} (Fin r)) ℤ _).span_eq,
    Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  apply Submodule.subset_span
  refine ⟨⟨(i.down.castSucc, Fin.last r), (Fin.castSucc_lt_last i.down).ne⟩, ?_⟩
  simpa only [Finsupp.coe_basisSingleOne] using diagonalRootDatum_root_castSucc_last i

section Points

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]

/-- The datum's root character is the weight through which the projective diagonal
torus rescales the corresponding elementary root subgroup. -/
theorem charOfPoint_ofAdd_diagonalRootDatum_root
    (p : CoordinateRootIndex (Fin (r + 1)))
    (t : WithConv
      (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin r) →₀ ℤ)) →ₐ[R] A)) :
    DiagonalizableGroup.charOfPoint t.ofConv
        (Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p)) =
      torusCharacter (SplitTorus.pointsMulEquiv t)
        (diagonalTorusWeight r (finProdFinEquiv p.1)) := by
  have hroot : Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p) =
      weightCharacter (diagonalTorusWeight r (finProdFinEquiv p.1)) := by
    apply Multiplicative.toAdd.injective
    ext i
    simp
  rw [hroot, charOfPoint_weightCharacter]

/-- The elementary root-subgroup conjugation formula, expressed using the roots
of the adjoint type-A datum. It holds over every commutative value algebra. -/
theorem diagonalTorus_mul_rootSubgroupPoints_mul_inv_eq_root
    (A : CommAlgCat.{v} R) (p : CoordinateRootIndex (Fin (r + 1)))
    (t : HopfAlgebra.points (R := R)
      (H := MonoidAlgebra R (SplitTorus.characterGroup (ULift.{u} (Fin r)))) A)
    (c : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    BialgHom.mapDomain (diagonalTorusCoordinateMap r R).hom t *
        rootSubgroupPoints A p.2 c *
        (BialgHom.mapDomain (diagonalTorusCoordinateMap r R).hom t)⁻¹ =
      rootSubgroupPoints A p.2
        ((AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).symm
          (Multiplicative.ofAdd
            ((DiagonalizableGroup.charOfPoint t.ofConv
                (Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p)) : Aˣ) •
              Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv c)))) := by
  -- The points functor wraps the character lattice as a categorical object.
  -- `erw` unfolds that object to match the explicit lattice in the character lemma.
  erw [charOfPoint_ofAdd_diagonalRootDatum_root]
  exact diagonalTorus_mul_rootSubgroupPoints_mul_inv A p.2 t c

end Points

end

end TauCeti.ProjectiveGeneralLinear
