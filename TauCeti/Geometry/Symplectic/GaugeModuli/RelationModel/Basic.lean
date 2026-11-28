/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.RepresentationTheory.SurfaceGroup.SpecialUnitary
public import TauCeti.Topology.Algebra.Matrix.ProjectiveSpecialLinearGroup.SpecialUnitary
public import TauCeti.Topology.Algebra.ProperAction.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Algebra.Group.Quotient
import TauCeti.Topology.Homeomorph.Quotient

/-!
# The twisted `SU(r)` representation model of surface moduli

Fix a rank `r : ℕ`, a complex scalar `ζ : ℂ`, and a genus `g : ℕ`. The **twisted relation set**
`TauCeti.relationSet r ζ g` (defined in `TauCeti.RepresentationTheory.SurfaceGroup.SpecialUnitary`)
consists of the tuples `(A₁, B₁, …, A_g, B_g)` in `SU(r)` satisfying the punctured-surface
relation

`⁅A₁, B₁⁆ ⋯ ⁅A_g, B_g⁆ = ζ • 1`,

where `⁅A, B⁆ = A * B * A⁻¹ * B⁻¹` is the group commutator. For positive rank `r ≥ 1` and a
primitive `r`-th root of unity `ζ = exp(2πi d / r)` (corresponding to `gcd(r, d) = 1`), the
quotient `TauCeti.GaugeModuli.relationModuli r ζ g` of `relationSet r ζ g` by simultaneous
conjugation is the representation model of the fixed-determinant coprime `U(r)` moduli space of
central-curvature connections on a closed oriented surface of genus `g` (Wehrheim–Woodward, *Floer
field theory for coprime rank and degree*, §3).

## Main definitions

* `TauCeti.GaugeModuli.commutatorProduct`: the ordered commutator product
  `(A₁, B₁, …, A_g, B_g) ↦ [A₁, B₁] ⋯ [A_g, B_g]` valued in `SU(r)`.
* `TauCeti.GaugeModuli.relationModuli`: the orbit quotient of `TauCeti.relationSet r ζ g` by
  simultaneous `SU(r)`-conjugation, with the quotient topology.
* `TauCeti.GaugeModuli.relationModuliEquivPSUOrbitQuotient`: homeomorphism identifying
  `relationModuli r ζ g` with the orbit space of the induced action of
  `PSU(r) = (Matrix.specialUnitaryGroup.toPSL).range`.

## Main results

* `TauCeti.GaugeModuli.continuous_commutatorProduct`,
  `TauCeti.GaugeModuli.mem_relationSet_iff_commutatorProduct`,
  `TauCeti.GaugeModuli.relationSet_eq_preimage_commutatorProduct`,
  `TauCeti.GaugeModuli.isClosed_relationSet`, `TauCeti.GaugeModuli.isCompact_relationSet`,
  `TauCeti.GaugeModuli.continuous_conjAct_smul_relationSet`, and
  `T2Space (relationModuli r ζ g)`: the commutator product is continuous with `relationSet r ζ g`
  as its coerced fiber, the relation set is compact, the simultaneous `SU(r)` conjugation map and
  induced `PSU(r)` action are continuous (with the `PSU(r)` action proper), and the quotient
  `relationModuli r ζ g` is compact Hausdorff.
* `TauCeti.GaugeModuli.eq_zero_of_commute_relationSet_of_trace_eq_zero`: vanishing of the
  trace-free commuting matrices (the infinitesimal stabilizer) at every solution when `ζ` is a
  primitive `r`-th root of unity (via `TauCeti.exists_eq_smul_one_of_commute_relationSet`).
* `TauCeti.GaugeModuli.conjAct_smul_relationSet_eq_self_iff`,
  `TauCeti.GaugeModuli.psu_smul_relationSet_eq_self_iff`,
  `TauCeti.GaugeModuli.stabilizer_psu_relationSet_eq_bot`, and
  `TauCeti.GaugeModuli.isCancelSMul_psu_relationSet`: when `ζ` is a primitive `r`-th root of
  unity, every `SU(r)`-stabilizer equals the center `Z(SU(r))` (which is isomorphic to `μ_r` for
  `r ≥ 1`, and trivial at `r = 0`)
  (`conjAct_smul_relationSet_eq_self_iff`, via `TauCeti.relationSet_stabilizer_central`), and the
  induced `PSU(r)` action on `relationSet r ζ g` is free (`psu_smul_relationSet_eq_self_iff`,
  `stabilizer_psu_relationSet_eq_bot`, `isCancelSMul_psu_relationSet`, hence faithful whenever
  `relationSet r ζ g` is nonempty).
* `TauCeti.GaugeModuli.isEmpty_relationModuli_zero`: the genus-zero moduli is empty for `r ≥ 2`
  and primitive `ζ`.
* `TauCeti.GaugeModuli.nonempty_relationModuli_rank_one` and
  `TauCeti.GaugeModuli.simplyConnectedSpace_relationModuli_rank_one`: for `r = 1` and `ζ = 1`, the
  moduli is a point (hence simply connected) in every genus.
* Continuous central-twist action of `(Z(SU(r)) × Z(SU(r)))^g` (representing `H¹(X; μ_r)` for
  `r ≥ 1`, and trivial at `r = 0`) on both `relationSet r ζ g` and `relationModuli r ζ g`.

## References

* Katrin Wehrheim and Chris T. Woodward, *Floer field theory for coprime rank and degree*,
  arXiv:1601.04924, §3 (Theorem 3.3.3 and Remark 3.3.7).
* Aliakbar Daemi, Kenji Fukaya, and Maksim Lipyanskiy, *Lagrangians, SO(3)-instantons and the
  Atiyah–Floer conjecture*, arXiv:2109.07032, Remark 2.2 and Lemma 2.43.
-/

public section

open Matrix Matrix.specialUnitaryGroup
open scoped commutatorElement

namespace TauCeti

namespace GaugeModuli

section Definitions

/-- Simultaneous conjugation of `SU(r)` restricts to `relationSet r ζ g`. -/
instance instMulActionConjActRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    MulAction (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationSet r ζ g) where
  smul u x := ⟨u • x.val, conjAct_smul_mem_relationSet u x.property⟩
  one_smul x := Subtype.ext (one_smul _ x.val)
  mul_smul u v x := Subtype.ext (mul_smul u v x.val)

@[simp]
theorem coe_conjAct_smul_relationSet {r : ℕ} {ζ : ℂ} {g : ℕ}
    (u : ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ)) (x : relationSet r ζ g) :
    ((u • x : relationSet r ζ g) :
      Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) =
      u • x.val :=
  (rfl)

/-- For arbitrary rank `r : ℕ`, scalar `ζ : ℂ`, and genus `g : ℕ`, the orbit quotient of
`relationSet r ζ g` by simultaneous `SU(r)`-conjugation, equipped with the quotient topology.
For positive rank `r ≥ 1` and a primitive `r`-th root of unity `ζ = exp(2πi d / r)` (coprime
degree `d`), this is the representation model `R_g / SU(r)` of the fixed-determinant coprime `U(r)`
moduli space of central-curvature connections on a closed oriented surface of genus `g`. -/
abbrev relationModuli (r : ℕ) (ζ : ℂ) (g : ℕ) : Type :=
  MulAction.orbitRel.Quotient (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationSet r ζ g)

end Definitions

section ActionsAndTopology

instance instContinuousConstSMulConjActRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    ContinuousConstSMul (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationSet r ζ g) where
  continuous_const_smul u :=
    continuous_induced_rng.mpr <|
      (continuous_const_smul u).comp continuous_subtypeVal

/-- Two elements of `relationSet r ζ g` have the same class in `relationModuli r ζ g` if and only
if they are simultaneously conjugate by some `u ∈ SU(r)`. -/
theorem quotient_mk_relationModuli_eq_iff {r : ℕ} {ζ : ℂ} {g : ℕ} (x y : relationSet r ζ g) :
    (Quotient.mk _ x : relationModuli r ζ g) = Quotient.mk _ y ↔
      ∃ u : Matrix.specialUnitaryGroup (Fin r) ℂ, ConjAct.toConjAct u • x.val = y.val := by
  rw [MulAction.quotientMk_eq_quotientMk_iff_exists_smul_eq]
  exact ⟨fun ⟨u, hu⟩ => ⟨ConjAct.ofConjAct u, congrArg Subtype.val hu⟩,
    fun ⟨u, hu⟩ => ⟨ConjAct.toConjAct u, Subtype.ext hu⟩⟩

/-- The ordered commutator product `(A₁, B₁, …, A_g, B_g) ↦ [A₁, B₁] ⋯ [A_g, B_g]` valued in
`SU(r)`. -/
def commutatorProduct (r g : ℕ)
    (x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) :
    Matrix.specialUnitaryGroup (Fin r) ℂ :=
  (List.ofFn fun j => ⁅(x j).1, (x j).2⁆).prod

/-- Evaluation of the ordered commutator product `commutatorProduct r g`. -/
@[simp]
theorem commutatorProduct_apply {r g : ℕ}
    (x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) :
    commutatorProduct r g x = (List.ofFn fun j => ⁅(x j).1, (x j).2⁆).prod := by
  unfold commutatorProduct
  rfl

/-- Membership in `relationSet r ζ g` as the coerced fiber of `commutatorProduct r g` over
`ζ • 1`. -/
theorem mem_relationSet_iff_commutatorProduct {r : ℕ} {ζ : ℂ} {g : ℕ}
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ} :
    x ∈ relationSet r ζ g ↔ (commutatorProduct r g x : Matrix (Fin r) (Fin r) ℂ) = ζ • 1 := by
  rw [mem_relationSet, commutatorProduct_apply]

/-- Characterization of `relationSet r ζ g` as the coerced fiber of `commutatorProduct r g` over
`ζ • 1`. -/
theorem relationSet_eq_preimage_commutatorProduct (r : ℕ) (ζ : ℂ) (g : ℕ) :
    relationSet r ζ g =
      (fun x => (commutatorProduct r g x : Matrix (Fin r) (Fin r) ℂ)) ⁻¹' {ζ • 1} := by
  ext x
  simp

/-- The ordered commutator product `commutatorProduct r g` is continuous. -/
theorem continuous_commutatorProduct (r g : ℕ) : Continuous (commutatorProduct r g) := by
  simp_rw [funext (fun x => commutatorProduct_apply x), List.ofFn_eq_map]
  refine continuous_list_prod (List.finRange g) fun j _ => ?_
  have hA : Continuous fun x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ ×
      Matrix.specialUnitaryGroup (Fin r) ℂ => (x j).1 :=
    continuous_fst.comp (continuous_apply j)
  have hB : Continuous fun x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ ×
      Matrix.specialUnitaryGroup (Fin r) ℂ => (x j).2 :=
    continuous_snd.comp (continuous_apply j)
  exact ((hA.mul hB).mul hA.inv).mul hB.inv

/-- The twisted relation set is closed in `(SU(r) × SU(r))^g`. -/
theorem isClosed_relationSet (r : ℕ) (ζ : ℂ) (g : ℕ) : IsClosed (relationSet r ζ g) := by
  rw [relationSet_eq_preimage_commutatorProduct]
  exact isClosed_singleton.preimage (continuous_subtypeVal.comp (continuous_commutatorProduct r g))

/-- The twisted relation set is compact. -/
theorem isCompact_relationSet (r : ℕ) (ζ : ℂ) (g : ℕ) : IsCompact (relationSet r ζ g) :=
  (isClosed_relationSet r ζ g).isCompact

instance instCompactSpaceRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    CompactSpace (relationSet r ζ g) :=
  isCompact_iff_compactSpace.mp (isCompact_relationSet r ζ g)

private theorem conjAct_toConjAct_smul_eq_self_iff {G : Type*} [Group G] (u a : G) :
    ConjAct.toConjAct u • a = a ↔ Commute u a := by
  rw [ConjAct.toConjAct_smul, mul_inv_eq_iff_eq_mul]
  rfl

/-- Central elements of `SU(r)` act trivially on `relationSet r ζ g`. -/
theorem conjAct_smul_relationSet_eq_self_of_mem_center {r : ℕ} {ζ : ℂ} {g : ℕ}
    {u : Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hu : u ∈ Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
    (x : relationSet r ζ g) : ConjAct.toConjAct u • x = x := by
  have hfix (a : Matrix.specialUnitaryGroup (Fin r) ℂ) : ConjAct.toConjAct u • a = a :=
    (conjAct_toConjAct_smul_eq_self_iff u a).mpr (Subgroup.mem_center_iff.mp hu a).symm
  exact Subtype.ext <| funext fun j => Prod.ext (hfix (x.val j).1) (hfix (x.val j).2)

/-- Projective conjugation of `PSU(r)` preserves the twisted relation set. -/
theorem psu_smul_mem_relationSet {r : ℕ} {ζ : ℂ} {g : ℕ}
    (p : (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range)
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hx : x ∈ relationSet r ζ g) : p • x ∈ relationSet r ζ g := by
  obtain ⟨u, rfl⟩ := toPSL.rangeRestrict_surjective p
  have heq :
      (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
          ProjectiveSpecialLinearGroup (Fin r) ℂ).rangeRestrict u • x =
        ConjAct.toConjAct u • x :=
    funext fun j => Prod.ext (toPSL_rangeRestrict_smul u (x j).1)
      (toPSL_rangeRestrict_smul u (x j).2)
  rw [heq]
  exact conjAct_smul_mem_relationSet _ hx

/-- The induced simultaneous conjugation action of `PSU(r)` on `relationSet r ζ g`, obtained by
restricting the coordinatewise projective conjugation action on `(SU(r) × SU(r))^g`. When `ζ` is
a primitive `r`-th root of unity, the action is free (`isCancelSMul_psu_relationSet`), and when
additionally `relationSet r ζ g` is nonempty, the action is faithful. -/
noncomputable instance instMulActionPSURelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    MulAction (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range (relationSet r ζ g) where
  smul p x := ⟨p • x.val, psu_smul_mem_relationSet p x.property⟩
  one_smul x := Subtype.ext (one_smul _ x.val)
  mul_smul p q x := Subtype.ext (mul_smul p q x.val)

@[simp]
theorem coe_psu_smul_relationSet {r : ℕ} {ζ : ℂ} {g : ℕ}
    (p : (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range)
    (x : relationSet r ζ g) :
    ((p • x : relationSet r ζ g) :
      Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) =
      p • x.val :=
  (rfl)

/-- On an element `toPSL.rangeRestrict u ∈ PSU(r)`, the `PSU(r)` action on `relationSet r ζ g`
agrees with simultaneous conjugation by `u ∈ SU(r)`. -/
@[simp]
theorem toPSL_rangeRestrict_smul_relationSet {r : ℕ} {ζ : ℂ} {g : ℕ}
    (u : Matrix.specialUnitaryGroup (Fin r) ℂ) (x : relationSet r ζ g) :
    (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).rangeRestrict u • x =
      ConjAct.toConjAct u • x :=
  Subtype.ext <| funext fun j =>
    Prod.ext (toPSL_rangeRestrict_smul u (x.val j).1) (toPSL_rangeRestrict_smul u (x.val j).2)

/-- The simultaneous conjugation map `SU(r) × relationSet r ζ g → relationSet r ζ g` is
continuous. -/
theorem continuous_conjAct_smul_relationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    Continuous fun p : Matrix.specialUnitaryGroup (Fin r) ℂ × relationSet r ζ g =>
      ConjAct.toConjAct p.1 • p.2 := by
  have hcoord (j : Fin g)
      (π : Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ →
        Matrix.specialUnitaryGroup (Fin r) ℂ) (hπ : Continuous π) :
      Continuous fun p : Matrix.specialUnitaryGroup (Fin r) ℂ × relationSet r ζ g =>
        p.1 * π (p.2.val j) * p.1⁻¹ :=
    (continuous_fst.mul
      (hπ.comp ((continuous_apply j).comp (continuous_subtypeVal.comp continuous_snd)))).mul
      continuous_fst.inv
  refine continuous_induced_rng.mpr ?_
  refine (continuous_pi fun j =>
    (hcoord j Prod.fst continuous_fst).prodMk (hcoord j Prod.snd continuous_snd)).congr ?_
  rintro ⟨u, x⟩
  refine funext fun j => ?_
  dsimp only [Function.comp_apply]
  rw [coe_conjAct_smul_relationSet]
  exact Prod.ext (ConjAct.toConjAct_smul u (x.val j).1).symm
    (ConjAct.toConjAct_smul u (x.val j).2).symm

instance instContinuousSMulPSURelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    ContinuousSMul (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range (relationSet r ζ g) where
  continuous_smul :=
    continuous_induced_rng.mpr <|
      (continuous_fst.smul (continuous_subtypeVal.comp continuous_snd)).congr fun ⟨p, x⟩ =>
        (coe_psu_smul_relationSet p x).symm

/-- The induced `PSU(r)` action on `relationSet r ζ g` is proper, since `PSU(r)` is compact
and `relationSet r ζ g` is Hausdorff. -/
instance instProperSMulPSURelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    ProperSMul (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range (relationSet r ζ g) :=
  TauCeti.properSMul_of_compactSpace _ _

/-- The moduli space `relationModuli r ζ g` is homeomorphic to the orbit space of the induced
`PSU(r)` action on `relationSet r ζ g`. -/
noncomputable def relationModuliEquivPSUOrbitQuotient (r : ℕ) (ζ : ℂ) (g : ℕ) :
    relationModuli r ζ g ≃ₜ
      MulAction.orbitRel.Quotient (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
        ProjectiveSpecialLinearGroup (Fin r) ℂ).range (relationSet r ζ g) :=
  Homeomorph.Quotient.congrRight fun _ _ => by
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff,
      MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨toPSL.rangeRestrict (ConjAct.ofConjAct u), by
        simpa [toPSL_rangeRestrict_smul_relationSet] using hu⟩
    · rintro ⟨p, hp⟩
      obtain ⟨u, rfl⟩ := toPSL.rangeRestrict_surjective p
      rw [toPSL_rangeRestrict_smul_relationSet] at hp
      exact ⟨ConjAct.toConjAct u, hp⟩

@[simp]
theorem relationModuliEquivPSUOrbitQuotient_mk {r : ℕ} {ζ : ℂ} {g : ℕ} (x : relationSet r ζ g) :
    relationModuliEquivPSUOrbitQuotient r ζ g (Quotient.mk _ x) = Quotient.mk'' x :=
  Homeomorph.Quotient.congrRight_mk _ x

@[simp]
theorem relationModuliEquivPSUOrbitQuotient_symm_mk {r : ℕ} {ζ : ℂ} {g : ℕ}
    (x : relationSet r ζ g) :
    (relationModuliEquivPSUOrbitQuotient r ζ g).symm (Quotient.mk'' x) = Quotient.mk _ x := by
  rw [← relationModuliEquivPSUOrbitQuotient_mk x, Homeomorph.symm_apply_apply]

/-- The representation model `relationModuli r ζ g` is Hausdorff, as the orbit space of the proper
`PSU(r)` action on `relationSet r ζ g`. -/
instance instT2SpaceRelationModuli (r : ℕ) (ζ : ℂ) (g : ℕ) : T2Space (relationModuli r ζ g) :=
  (relationModuliEquivPSUOrbitQuotient r ζ g).isEmbedding.t2Space

end ActionsAndTopology

section IrreducibilityAndStabilizers

/-- **Vanishing of the trace-free infinitesimal stabilizer.** For a primitive `r`-th root of unity
`ζ`, every trace-free complex matrix commuting with all entries of a solution
`x ∈ relationSet r ζ g` vanishes. -/
theorem eq_zero_of_commute_relationSet_of_trace_eq_zero {r : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) {g : ℕ}
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hx : x ∈ relationSet r ζ g) (M : Matrix (Fin r) (Fin r) ℂ)
    (hM : ∀ j, Commute M ((x j).1 : Matrix (Fin r) (Fin r) ℂ) ∧
      Commute M ((x j).2 : Matrix (Fin r) (Fin r) ℂ))
    (htr : M.trace = 0) : M = 0 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact Subsingleton.elim _ _
  obtain ⟨c, rfl⟩ := exists_eq_smul_one_of_commute_relationSet hζ hx M hM
  have hc : (r : ℂ) * c = 0 := by
    simpa [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, mul_comm] using htr
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc0 : c = 0 := (mul_eq_zero.mp hc).resolve_left hr0
  simp [hc0]

/-- When `ζ` is a primitive `r`-th root of unity, an element `u ∈ SU(r)` stabilizes
`x : relationSet r ζ g` under simultaneous conjugation if and only if `u` lies in the center of
`SU(r)`. -/
@[simp]
theorem conjAct_smul_relationSet_eq_self_iff {r : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) {g : ℕ} (x : relationSet r ζ g)
    (u : Matrix.specialUnitaryGroup (Fin r) ℂ) :
    ConjAct.toConjAct u • x = x ↔
      u ∈ Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) := by
  constructor
  · intro h
    refine TauCeti.relationSet_stabilizer_central hζ x.property fun j => ?_
    have hj : ConjAct.toConjAct u • x.val j = x.val j := congrFun (congrArg Subtype.val h) j
    exact ⟨(conjAct_toConjAct_smul_eq_self_iff u _).mp (congrArg Prod.fst hj),
      (conjAct_toConjAct_smul_eq_self_iff u _).mp (congrArg Prod.snd hj)⟩
  · exact fun hu => conjAct_smul_relationSet_eq_self_of_mem_center hu x

/-- **Freeness of the induced `PSU(r)` action.** For a primitive `r`-th root of unity `ζ`, an
element of `PSU(r)` fixes a point `x : relationSet r ζ g` if and only if it is `1` (so the action
is faithful whenever `relationSet r ζ g` is nonempty). -/
@[simp]
theorem psu_smul_relationSet_eq_self_iff {r : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) {g : ℕ} (x : relationSet r ζ g)
    (p : (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range) :
    p • x = x ↔ p = 1 := by
  constructor
  · intro hp
    obtain ⟨u, rfl⟩ := toPSL.rangeRestrict_surjective p
    rw [toPSL_rangeRestrict_smul_relationSet, conjAct_smul_relationSet_eq_self_iff hζ x u,
      ← Matrix.specialUnitaryGroup.ker_toPSL_eq_center, MonoidHom.mem_ker] at hp
    exact Subtype.ext hp
  · rintro rfl
    exact one_smul _ x

/-- The `PSU(r)`-stabilizer of every point of `relationSet r ζ g` is trivial when `ζ` is a
primitive `r`-th root of unity. -/
@[simp]
theorem stabilizer_psu_relationSet_eq_bot {r : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) {g : ℕ} (x : relationSet r ζ g) :
    MulAction.stabilizer (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range x = ⊥ := by
  ext p
  simp [MulAction.mem_stabilizer_iff, psu_smul_relationSet_eq_self_iff hζ x p]

/-- When `ζ` is a primitive `r`-th root of unity, the induced `PSU(r)` action on
`relationSet r ζ g` is free (`IsCancelSMul`). -/
theorem isCancelSMul_psu_relationSet {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r) (g : ℕ) :
    IsCancelSMul (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range (relationSet r ζ g) :=
  isCancelSMul_iff_stabilizer_eq_bot.mpr (stabilizer_psu_relationSet_eq_bot hζ)

end IrreducibilityAndStabilizers

section BoundaryCases

/-- For `r ≥ 2` and a primitive `r`-th root of unity `ζ`, the genus-zero relation set is empty. -/
theorem isEmpty_relationSet_zero {r : ℕ} (hr : 2 ≤ r) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r) :
    IsEmpty (relationSet r ζ 0) := by
  have hne : ζ ≠ 1 := hζ.ne_one (by omega)
  rw [TauCeti.relationSet_zero_eq_empty (by omega) hne]
  infer_instance

/-- For `r ≥ 2` and a primitive `r`-th root of unity `ζ`, the genus-zero (sphere) moduli is
empty. -/
theorem isEmpty_relationModuli_zero {r : ℕ} (hr : 2 ≤ r) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r) :
    IsEmpty (relationModuli r ζ 0) := by
  have : IsEmpty (relationSet r ζ 0) := isEmpty_relationSet_zero hr hζ
  infer_instance

/-- When `Fin r` is a subsingleton (`r ≤ 1`), `SU(r)` and `relationSet r ζ g` are subsingletons. -/
instance instSubsingletonRelationSet {r : ℕ} [Subsingleton (Fin r)] (ζ : ℂ) (g : ℕ) :
    Subsingleton (relationSet r ζ g) := by
  have : Subsingleton (Matrix.specialUnitaryGroup (Fin r) ℂ) :=
    Matrix.specialUnitaryGroup.toSL_injective.subsingleton
  infer_instance

/-- At rank one with `ζ = 1`, the relation set is nonempty in every genus. -/
theorem nonempty_relationSet_rank_one {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 1) (g : ℕ) :
    Nonempty (relationSet 1 ζ g) :=
  ⟨⟨1, by rw [IsPrimitiveRoot.one_right_iff.mp hζ]; exact one_mem_relationSet 1 g⟩⟩

/-- At rank one with a primitive `1`-st root of unity (`ζ = 1`), the moduli space is nonempty in
every genus (and a subsingleton by `instSubsingletonRelationSet`). -/
theorem nonempty_relationModuli_rank_one {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 1) (g : ℕ) :
    Nonempty (relationModuli 1 ζ g) := by
  obtain ⟨x⟩ := nonempty_relationSet_rank_one hζ g
  exact ⟨Quotient.mk _ x⟩

/-- At rank one with `ζ = 1`, the moduli space is simply connected in every genus. -/
theorem simplyConnectedSpace_relationModuli_rank_one {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 1) (g : ℕ) :
    SimplyConnectedSpace (relationModuli 1 ζ g) := by
  -- `Subsingleton` is inferred via `Quotient.instSubsingletonQuotient`; only `Nonempty` is needed.
  have : Nonempty (relationModuli 1 ζ g) := nonempty_relationModuli_rank_one hζ g
  exact SimplyConnectedSpace.ofContractible _

end BoundaryCases

section CentralTwistAction

/-- The central-twist action of `(Z(SU(r)) × Z(SU(r)))^g` (representing `H¹(X; μ_r)` for
`r ≥ 1`, and trivial at `r = 0`) on `relationSet r ζ g`, multiplying each entry `(A_j, B_j)` by
`(z_{1,j}, z_{2,j})`. -/
instance instMulActionCenterTwistRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    MulAction
      (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
        Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
      (relationSet r ζ g) where
  smul ε x := ⟨fun j => ((ε j).1.val * (x.val j).1, (ε j).2.val * (x.val j).2),
    center_mul_mem_relationSet ε x.property⟩
  one_smul _ := Subtype.ext <| funext fun _ => Prod.ext (one_mul _) (one_mul _)
  mul_smul _ _ _ := Subtype.ext <| funext fun _ => Prod.ext (mul_assoc _ _ _) (mul_assoc _ _ _)

@[simp]
theorem coe_centerTwist_smul_relationSet {r : ℕ} {ζ : ℂ} {g : ℕ}
    (ε : Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
    (x : relationSet r ζ g) (j : Fin g) :
    ((ε • x : relationSet r ζ g).val j) =
      ((ε j).1.val * (x.val j).1, (ε j).2.val * (x.val j).2) :=
  (rfl)

instance instContinuousSMulCenterTwistRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    ContinuousSMul
      (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
        Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
      (relationSet r ζ g) where
  continuous_smul := by
    have hcoord (j : Fin g)
        (π₁ : Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
            Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) →
          Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (hπ₁ : Continuous π₁)
        (π₂ : Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ →
          Matrix.specialUnitaryGroup (Fin r) ℂ) (hπ₂ : Continuous π₂) :
        Continuous fun p :
          (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
            Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) × relationSet r ζ g =>
          (π₁ (p.1 j)).val * π₂ (p.2.val j) :=
      (continuous_subtypeVal.comp (hπ₁.comp ((continuous_apply j).comp continuous_fst))).mul
        (hπ₂.comp ((continuous_apply j).comp (continuous_subtypeVal.comp continuous_snd)))
    refine continuous_induced_rng.mpr ?_
    refine (continuous_pi fun j =>
      (hcoord j Prod.fst continuous_fst Prod.fst continuous_fst).prodMk
        (hcoord j Prod.snd continuous_snd Prod.snd continuous_snd)).congr ?_
    rintro ⟨ε, x⟩
    exact funext fun j => (coe_centerTwist_smul_relationSet ε x j).symm

/-- Central twists commute with simultaneous `SU(r)`-conjugation on `relationSet r ζ g`. -/
instance instSMulCommClassCenterTwistConjAct (r : ℕ) (ζ : ℂ) (g : ℕ) :
    SMulCommClass
      (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
        Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
      (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
      (relationSet r ζ g) where
  smul_comm ε u x := by
    have hcoord (z : Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
        (a : Matrix.specialUnitaryGroup (Fin r) ℂ) :
        z.val * (u • a) = u • (z.val * a) := by
      rw [ConjAct.smul_def, ConjAct.smul_def, ← mul_assoc, ← mul_assoc,
        ← Subgroup.mem_center_iff.mp z.property (ConjAct.ofConjAct u),
        mul_assoc (ConjAct.ofConjAct u)]
    refine Subtype.ext <| funext fun j => ?_
    simp only [coe_centerTwist_smul_relationSet, coe_conjAct_smul_relationSet, Pi.smul_apply,
      Prod.ext_iff, Prod.smul_fst, Prod.smul_snd]
    exact ⟨hcoord (ε j).1 (x.val j).1, hcoord (ε j).2 (x.val j).2⟩

/-- Central twists commute with the induced `PSU(r)` action on `relationSet r ζ g`. -/
instance instSMulCommClassCenterTwistPSU (r : ℕ) (ζ : ℂ) (g : ℕ) :
    SMulCommClass
      (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
        Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
      (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
        ProjectiveSpecialLinearGroup (Fin r) ℂ).range
      (relationSet r ζ g) where
  smul_comm ε p x := by
    obtain ⟨u, rfl⟩ := toPSL.rangeRestrict_surjective p
    rw [toPSL_rangeRestrict_smul_relationSet, toPSL_rangeRestrict_smul_relationSet, smul_comm]

/-- The homeomorphism between `relationModuli r ζ g` and the `PSU(r)` orbit quotient is
equivariant with respect to the central-twist action. -/
@[simp]
theorem relationModuliEquivPSUOrbitQuotient_smul {r : ℕ} {ζ : ℂ} {g : ℕ}
    (ε : Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
    (q : relationModuli r ζ g) :
    relationModuliEquivPSUOrbitQuotient r ζ g (ε • q) =
      ε • relationModuliEquivPSUOrbitQuotient r ζ g q :=
  Quotient.inductionOn q fun _ => by
    simp only [MulAction.orbitRel.Quotient.smul_mk, relationModuliEquivPSUOrbitQuotient_mk]

/-- The inverse homeomorphism between `relationModuli r ζ g` and the `PSU(r)` orbit quotient
is equivariant with respect to the central-twist action. -/
@[simp]
theorem relationModuliEquivPSUOrbitQuotient_symm_smul {r : ℕ} {ζ : ℂ} {g : ℕ}
    (ε : Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
    (q : MulAction.orbitRel.Quotient (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range (relationSet r ζ g)) :
    (relationModuliEquivPSUOrbitQuotient r ζ g).symm (ε • q) =
      ε • (relationModuliEquivPSUOrbitQuotient r ζ g).symm q :=
  Quotient.inductionOn q fun _ => by
    simp only [MulAction.orbitRel.Quotient.smul_mk, relationModuliEquivPSUOrbitQuotient_symm_mk]

/-- The central-twist action on `relationModuli r ζ g` is continuous. -/
instance instContinuousSMulCenterTwistRelationModuli (r : ℕ) (ζ : ℂ) (g : ℕ) :
    ContinuousSMul
      (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
        Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
      (relationModuli r ζ g) where
  continuous_smul := by
    rw [← (IsOpenQuotientMap.id.prodMap
      (MulAction.isOpenQuotientMap_quotientMk (Γ := ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
        (T := relationSet r ζ g))).continuous_comp_iff,
      MulAction.orbitRel.Quotient.smul_comp_prodMap_mk]
    exact continuous_quot_mk.comp continuous_smul

end CentralTwistAction

end GaugeModuli

end TauCeti
