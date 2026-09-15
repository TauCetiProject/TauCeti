/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.CarrierSpecialIsogeny
public import TauCeti.Algebra.Lie.G2.ShortRoot.PinnedCrossProduct
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.ConstantForm
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.ConstantMultiplication

/-!
# The special isogeny on the points of the short-root type-G2 carrier

`Matrix.g2SpecialIsogeny` is multiplicative in characteristic three on matrices preserving the
invariant cross product of the seven-dimensional module of type `G₂`, the left factor also fixing
the invariant dual form by congruence. This file shows that every matrix point of the short-root
carrier satisfies both conditions, so that in characteristic three the minor formula is a
homomorphism on the carrier's group of points, and reads it on the pinned generators.

Both conditions are closed conditions on `GL₇` cut out by a Hopf ideal: the first is the
multiplication with structure matrices `TauCeti.G2ShortRoot.crossOperator`, the second the
constant form `TauCeti.G2ShortRoot.invariantDualForm`. The carrier is the smallest closed
subgroup scheme of `GL₇` containing the represented simple root subgroups and the weight torus,
so each containment is tested on those generators, where it is the statement already proved for
the divided-power exponential matrices `1 + t X + t² Y` and for the weight-diagonal matrices.

## What is not here

The homomorphism below has the ambient general linear group as its codomain. That the matrix of
the image is again a point of the carrier is a statement about the carrier as a group scheme over
`𝔽₃`, and the minor formula is multiplicative only there: it is a homomorphism out of the base
change of the carrier along `ℤ → 𝔽₃`, while the defining ideal of the carrier is maximal among
Hopf ideals killed by the generating coordinate maps over `ℤ` only. Over a base that is not flat
new equations may appear, so the base change of the carrier need not be the closed subgroup
scheme generated over `𝔽₃` by the base-changed generators, and the maximality that would place
the image back inside the carrier is not available. Consequently nothing below iterates the
formula on a general point, and no identity of endomorphisms is asserted; the square relation
against the carrier's Frobenius is the one on the pinned generators.

The carrier is not identified with the pinned simply connected group scheme of type `G₂`, and
constructions made here transfer to that group scheme only along such an identification.

## Main definitions

* `TauCeti.G2ShortRoot.specialIsogeny`: the special isogeny of the carrier's points in
  characteristic three, valued in `GL₇`.

## Main results

* `TauCeti.G2ShortRoot.preservesG2Cross_of_mem_points` and
  `TauCeti.G2ShortRoot.preservesDualForm_of_mem_points`: **every point of the carrier preserves
  the cross product and fixes the invariant dual form by congruence**, over every commutative
  ring.
* `TauCeti.G2ShortRoot.g2SpecialIsogeny_mul_of_mem_points`: **the minor formula is multiplicative
  on the carrier's points** in characteristic three.
* `TauCeti.G2ShortRoot.specialIsogeny_rootSubgroupPoints` and
  `TauCeti.G2ShortRoot.specialIsogeny_weightTorusPoints`: the pinning equations and the torus
  equation for that homomorphism.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* S. Garibaldi and R. M. Guralnick, *Simple groups stabilizing polynomials*, Forum of Mathematics
  Pi **3** (2015), §6, for the cross product and the quotient by the short-root ideal.
-/

public section

open Matrix

namespace TauCeti.G2ShortRoot

open TauCeti.UniversalEnvelopingAlgebra

universe v

local notation "rootGen" => TauCeti.serreRootGenerator _root_.CartanMatrix.G₂
local notation "cartanGen" => TauCeti.serreH ℚ _root_.CartanMatrix.G₂

variable {A : Type v} [CommRing A]

/-- Preserving the type-`G₂` cross product is preserving the constant multiplication whose
structure matrices are the cross-product operators. -/
theorem preserves_crossOperator_iff_preservesG2Cross (g : Matrix (Fin 7) (Fin 7) A) :
    ConstantMultiplication.Preserves ℤ 7 crossOperator g ↔ PreservesG2Cross g := by
  rw [ConstantMultiplication.preserves_def, preservesG2Cross_def]
  simp only [ConstantMultiplication.imageStructureMatrix_def, algebraMap_int_eq,
    Int.coe_castRingHom]

/-- A represented root-subgroup matrix of the short-root carrier is a numbered simple-root point
of it. -/
private theorem kostantRootSubgroupMatrix_eq_rootSubgroupPoints (k : Fin 2 ⊕ Fin 2) (B : Type)
    [CommRing B] (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] B)) :
    kostantRootSubgroupMatrix rootGen cartanGen rep lattice.toAddSubgroup
        rep_kostantForm_mem_lattice k (isNilpotent_rep_serreRootGenerator k) latticeBasis q =
      (rootSubgroupPoints k B (AdditiveGroup.gaPointsMulEquiv q) :
        _root_.Matrix.GeneralLinearGroup (Fin 7) B) := by
  rw [coe_rootSubgroupPoints_eq_kostantRootSubgroupMatrix, MulEquiv.symm_apply_apply]

/-- A represented weight-torus matrix of the short-root carrier is the diagonal matrix of the
weight characters. -/
private theorem coe_kostantTorusMatrix_eq_diagonal (B : Type) [CommRing B] (s : Fin 2 → Bˣ) :
    ((kostantTorusMatrix lattice.toAddSubgroup latticeBasis weight s :
        _root_.Matrix.GeneralLinearGroup (Fin 7) B) : Matrix (Fin 7) (Fin 7) B) =
      Matrix.diagonal fun a => (torusCharacter s (weight a) : B) := by
  rw [kostantTorusMatrix_apply, diagGL_coe]

/-- A point of the short-root carrier is a point of the toral Kostant closure it is defined as.
The module boundary hides that definition, so the two presentations of the defining ideal are
compared explicitly. -/
private theorem mem_kostantToralPointsSubgroup_of_mem_points
    {g : _root_.Matrix.GeneralLinearGroup (Fin 7) A} (hg : g ∈ points A) :
    g ∈ kostantToralPointsSubgroup rootGen cartanGen rep lattice.toAddSubgroup
      rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis weight A := by
  rw [kostantToralPointsSubgroup_def, ← definingIdeal_def, ← points_def]
  exact hg

/-- **Every point of the short-root type-`G₂` carrier preserves the cross product**, over every
commutative ring. -/
theorem preservesG2Cross_of_mem_points {g : _root_.Matrix.GeneralLinearGroup (Fin 7) A}
    (hg : g ∈ points A) :
    PreservesG2Cross ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) := by
  rw [← preserves_crossOperator_iff_preservesG2Cross]
  refine preserves_of_mem_kostantToralPointsSubgroup_of_generators
    rootGen cartanGen rep lattice.toAddSubgroup rep_kostantForm_mem_lattice
    isNilpotent_rep_serreRootGenerator latticeBasis weight crossOperator
    (fun k B _ q => ?_) (fun B _ instF s => ?_) A
    (mem_kostantToralPointsSubgroup_of_mem_points hg)
  · rw [kostantRootSubgroupMatrix_eq_rootSubgroupPoints,
      preserves_crossOperator_iff_preservesG2Cross]
    exact preservesG2Cross_coe_rootSubgroupPoints k _
  · -- The criterion quantifies over the enumerations of the weight index type, all of which
    -- agree with the standard one.
    obtain rfl : instF = Fin.fintype 2 := Subsingleton.elim _ _
    rw [coe_kostantTorusMatrix_eq_diagonal, preserves_crossOperator_iff_preservesG2Cross]
    exact preservesG2Cross_weightTorusMatrix s

/-- **Every point of the short-root type-`G₂` carrier fixes the invariant dual form by
congruence**, over every commutative ring. -/
theorem preservesDualForm_of_mem_points {g : _root_.Matrix.GeneralLinearGroup (Fin 7) A}
    (hg : g ∈ points A) :
    ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) *
        invariantDualForm.map (Int.cast : ℤ → A) *
        ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A)ᵀ =
      invariantDualForm.map (Int.cast : ℤ → A) := by
  have key := mul_mul_transpose_of_mem_kostantToralPointsSubgroup_of_generators
    rootGen cartanGen rep lattice.toAddSubgroup rep_kostantForm_mem_lattice
    isNilpotent_rep_serreRootGenerator latticeBasis weight invariantDualForm
    (fun k B _ q => by
      rw [kostantRootSubgroupMatrix_eq_rootSubgroupPoints]
      simpa only [algebraMap_int_eq, Int.coe_castRingHom] using
        preservesDualForm_coe_rootSubgroupPoints k (AdditiveGroup.gaPointsMulEquiv q))
    (fun B _ s => by
      rw [coe_kostantTorusMatrix_eq_diagonal]
      simpa only [algebraMap_int_eq, Int.coe_castRingHom] using
        preservesDualForm_weightTorusMatrix s)
    A (mem_kostantToralPointsSubgroup_of_mem_points hg)
  simpa only [algebraMap_int_eq, Int.coe_castRingHom] using key

/-- **The special isogeny is multiplicative on the points of the short-root type-`G₂` carrier** in
characteristic three. -/
theorem g2SpecialIsogeny_mul_of_mem_points [CharP A 3]
    {g h : _root_.Matrix.GeneralLinearGroup (Fin 7) A} (hg : g ∈ points A) (hh : h ∈ points A) :
    g2SpecialIsogeny (((g * h : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A)) =
      g2SpecialIsogeny ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
          Matrix (Fin 7) (Fin 7) A) *
        g2SpecialIsogeny ((h : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
          Matrix (Fin 7) (Fin 7) A) := by
  rw [Units.val_mul]
  exact g2SpecialIsogeny_mul (preservesG2Cross_of_mem_points hg)
    (preservesDualForm_of_mem_points hg) (preservesG2Cross_of_mem_points hh)

variable (A) in
/-- The image of a carrier point under the minor formula is inverse to the image of its
inverse. -/
private theorem g2SpecialIsogeny_mul_g2SpecialIsogeny_inv [CharP A 3] (g : points A) :
    g2SpecialIsogeny ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
          Matrix (Fin 7) (Fin 7) A) *
        g2SpecialIsogeny (((g⁻¹ : points A) : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
          Matrix (Fin 7) (Fin 7) A) = 1 := by
  rw [← g2SpecialIsogeny_mul_of_mem_points g.2 (g⁻¹ : points A).2,
    ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one, g2SpecialIsogeny_one]

variable (A) in
private theorem g2SpecialIsogeny_inv_mul_g2SpecialIsogeny [CharP A 3] (g : points A) :
    g2SpecialIsogeny (((g⁻¹ : points A) : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
          Matrix (Fin 7) (Fin 7) A) *
        g2SpecialIsogeny ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
          Matrix (Fin 7) (Fin 7) A) = 1 := by
  rw [← g2SpecialIsogeny_mul_of_mem_points (g⁻¹ : points A).2 g.2,
    ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one, g2SpecialIsogeny_one]

/-- **The special isogeny of the short-root type-`G₂` carrier in characteristic three**: the minor
formula on the carrier's points, valued in the ambient general linear group. -/
noncomputable def specialIsogeny (A : Type v) [CommRing A] [CharP A 3] :
    points A →* _root_.Matrix.GeneralLinearGroup (Fin 7) A :=
  MonoidHom.mk'
    (fun g => ⟨g2SpecialIsogeny ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A),
      g2SpecialIsogeny (((g⁻¹ : points A) : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A),
      g2SpecialIsogeny_mul_g2SpecialIsogeny_inv A g,
      g2SpecialIsogeny_inv_mul_g2SpecialIsogeny A g⟩)
    fun g h => Units.ext (g2SpecialIsogeny_mul_of_mem_points g.2 h.2)

/-- The matrix of the special isogeny at a carrier point is the minor formula at its matrix. -/
@[simp]
theorem coe_specialIsogeny [CharP A 3] (g : points A) :
    ((specialIsogeny A g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) =
      g2SpecialIsogeny ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) := by
  rw [specialIsogeny]
  rfl

/-- **The pinning equations of the special isogeny on the carrier's numbered simple root
subgroups**: the numbered simple-root point at `k` goes to the one at the length-exchanged index,
with the parameter raised to the exponent of `k`, three at the short node and one at the long
node. -/
@[simp]
theorem specialIsogeny_rootSubgroupPoints [CharP A 3] (k : Fin 2 ⊕ Fin 2) (t : A) :
    specialIsogeny A (rootSubgroupPoints k A (Multiplicative.ofAdd t)) =
      (rootSubgroupPoints (specialIsogenyRootIndex k) A
        (Multiplicative.ofAdd (t ^ specialIsogenyExponent k)) :
        _root_.Matrix.GeneralLinearGroup (Fin 7) A) :=
  Units.ext (by rw [coe_specialIsogeny, g2SpecialIsogeny_coe_rootSubgroupPoints])

/-- **The torus equation of the special isogeny**: a point of the carrier's split weight torus
goes to the point of the length-exchanged coordinates `(s₁, s₀³)`. -/
@[simp]
theorem specialIsogeny_weightTorusPoints [CharP A 3] (s : Fin 2 → Aˣ) :
    specialIsogeny A (weightTorusPoints A s) =
      (weightTorusPoints A (specialIsogenyTorusMap s) :
        _root_.Matrix.GeneralLinearGroup (Fin 7) A) :=
  Units.ext (by rw [coe_specialIsogeny, g2SpecialIsogeny_coe_weightTorusPoints])

end TauCeti.G2ShortRoot
