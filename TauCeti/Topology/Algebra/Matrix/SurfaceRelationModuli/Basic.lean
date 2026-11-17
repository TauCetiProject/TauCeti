/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Homeomorph.Quotient
public import TauCeti.Analysis.Matrix.UnitaryGroup.SpecialUnitary
public import TauCeti.Topology.Algebra.UnitaryGroup
import Mathlib.Topology.Algebra.MulAction
import TauCeti.GroupTheory.Commutator
import TauCeti.GroupTheory.GroupAction.ConjAct
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# Twisted `SU(r)` surface commutator relation moduli

For natural numbers `r` and `g` and a complex scalar `ζ`, this file defines and studies the twisted
surface commutator relation set `TauCeti.SpecialUnitary.relationSet r ζ g` inside
`Fin g → SU(r) × SU(r)` (`SU(r) = Matrix.specialUnitaryGroup (Fin r) ℂ`), cut out by the equation

`⁅A₁, B₁⁆ * ⋯ * ⁅A_g, B_g⁆ = ζ • 1`

with Mathlib's group commutator convention `⁅A, B⁆ = A * B * A⁻¹ * B⁻¹`, together with its quotient
`TauCeti.SpecialUnitary.relationModuli r ζ g` by simultaneous `SU(r)`-conjugation carrying the
quotient topology. When `ζ = exp (2πi d / r)`, the primitive-root condition `IsPrimitiveRoot ζ r`
expresses coprimality `gcd(r, d) = 1`; the quotient is then the finite-dimensional holonomy model
of the fixed-determinant central-curvature moduli space on a closed oriented surface of genus `g`.

Genus-one existence, uniqueness up to conjugation, simple connectivity, and genus-one witnesses are
established in `TauCeti.Topology.Algebra.Matrix.SurfaceRelationModuli.GenusOne`.

## Main definitions

* `TauCeti.SpecialUnitary.relationSet`: tuples `(A₁, B₁, …, A_g, B_g)` in `SU(r)` whose ordered
  product of group commutators equals `ζ • 1`.
* `TauCeti.SpecialUnitary.relationSubMulAction`: `relationSet r ζ g` as a `SubMulAction` of
  `ConjAct (SU(r))`.
* `TauCeti.SpecialUnitary.relationModuli`: the quotient of `relationSet r ζ g` by simultaneous
  `SU(r)`-conjugation, with the quotient topology.
* `TauCeti.SpecialUnitary.relationModuliMk`: the open quotient projection
  `relationSet r ζ g → relationModuli r ζ g`, invariant under `ConjAct (SU(r))`
  (`TauCeti.SpecialUnitary.relationModuliMk_conjAct_smul`).
* `TauCeti.SpecialUnitary.instMulActionQuotientCenterRelationSet`: the descended conjugation action
  of `SU(r) ⧸ Subgroup.center (SU(r))` on `relationSet r ζ g`, with homeomorphism
  `TauCeti.SpecialUnitary.relationModuliHomeomorphQuotientCenter` identifying `relationModuli` with
  its orbit space (`TauCeti.SpecialUnitary.relationModuliHomeomorphQuotientCenter_mk`).
* `TauCeti.SpecialUnitary.instMulActionCenterTwistRelationSet` and
  `TauCeti.SpecialUnitary.instMulActionCenterTwistRelationModuli`: the continuous entrywise central
  root-of-unity twist action of `Fin g → center(SU(r)) × center(SU(r))` on `relationSet` and its
  descent to `relationModuli`.

## Main results

* `TauCeti.SpecialUnitary.isClosed_relationSet`, `TauCeti.SpecialUnitary.isCompact_relationSet`,
  `TauCeti.SpecialUnitary.instCompactSpaceRelationModuli`,
  `TauCeti.SpecialUnitary.instT2SpaceRelationModuli`: `relationSet r ζ g` is closed and compact, and
  `relationModuli r ζ g` is compact and Hausdorff.
* `TauCeti.SpecialUnitary.relationSet_stabilizer_central`: when `IsPrimitiveRoot ζ r`, every
  `u ∈ SU(r)` commuting with all entries of a point of `relationSet r ζ g` lies in the center of
  `SU(r)`; equivalently (`TauCeti.SpecialUnitary.conjAct_toConjAct_smul_eq_self_iff_mem_center`)
  every conjugation stabilizer equals `Subgroup.center (SU(r))`, and the descended action of
  `SU(r) ⧸ Subgroup.center (SU(r))` on `relationSet r ζ g` is free
  (`TauCeti.SpecialUnitary.isCancelSMul_quotientCenter_relationSet`).
* `TauCeti.SpecialUnitary.isEmpty_relationModuli_zero` and
  `TauCeti.SpecialUnitary.isEmpty_relationModuli_zero_of_isPrimitiveRoot`: on the sphere (`g = 0`),
  the moduli is empty whenever `1 ≤ r` and `ζ ≠ 1`, in particular whenever `2 ≤ r` and
  `IsPrimitiveRoot ζ r`.
* `TauCeti.SpecialUnitary.subsingleton_relationModuli_of_le_one` and
  `TauCeti.SpecialUnitary.simplyConnectedSpace_relationModuli_of_le_one`: for `r ≤ 1` and `ζ = 1`,
  `relationModuli r 1 g` is a single point (hence simply connected) for every genus `g`.

## References

* M. F. Atiyah, R. Bott, *The Yang-Mills equations over Riemann surfaces*, Philos. Trans. Roy. Soc.
  London Ser. A **308** (1983), 523-615, §9.
* K. Wehrheim, C. T. Woodward, *Floer field theory for coprime rank and degree*, Geom. Topol.
  **20** (2016), 3135-3188, §3.3.
* A. Daemi, K. Fukaya, M. Lipyanskiy, *Lagrangians, SO(3)-instantons and the Atiyah-Floer
  conjecture*, arXiv:2109.07032, §2.
-/

public section

open Matrix Topology
open scoped commutatorElement

namespace TauCeti.SpecialUnitary

/-! ### The twisted commutator relation set and conjugation quotient -/

/-- The twisted surface commutator relation set in `SU(r)`: tuples `(A₁, B₁, …, A_g, B_g)` in
`Matrix.specialUnitaryGroup (Fin r) ℂ` whose ordered product of group commutators
`⁅A₁, B₁⁆ * ⋯ * ⁅A_g, B_g⁆` equals the scalar matrix `ζ • 1`. -/
def relationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    Set (Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) :=
  {x | ((List.ofFn fun j => ⁅(x j).1, (x j).2⁆).prod : Matrix (Fin r) (Fin r) ℂ) = ζ • 1}

/-- Membership in `relationSet r ζ g` is equality of the ordered commutator product with `ζ • 1`. -/
@[simp]
theorem mem_relationSet_iff {r : ℕ} {ζ : ℂ} {g : ℕ}
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ} :
    x ∈ relationSet r ζ g ↔
      ((List.ofFn fun j => ⁅(x j).1, (x j).2⁆).prod : Matrix (Fin r) (Fin r) ℂ) = ζ • 1 :=
  (Iff.rfl)

/-- At genus `0`, membership in `relationSet r ζ 0` reduces to `1 = ζ • 1` in
`Matrix (Fin r) (Fin r) ℂ`. -/
theorem mem_relationSet_zero_iff {r : ℕ} {ζ : ℂ}
    {x : Fin 0 → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ} :
    x ∈ relationSet r ζ 0 ↔ (1 : Matrix (Fin r) (Fin r) ℂ) = ζ • 1 := by
  simp [mem_relationSet_iff]

/-- At genus `1`, membership in `relationSet r ζ 1` is the single commutator equation
`⁅(x 0).1, (x 0).2⁆ = ζ • 1`. -/
theorem mem_relationSet_one_iff {r : ℕ} {ζ : ℂ}
    {x : Fin 1 → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ} :
    x ∈ relationSet r ζ 1 ↔
      (↑⁅(x 0).1, (x 0).2⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1 := by
  simp [mem_relationSet_iff, List.ofFn_succ]

/-- Simultaneous conjugation by `ConjAct (SU(r))` preserves `relationSet r ζ g`: conjugation is a
group automorphism, and fixes the scalar matrix `ζ • 1`. -/
theorem conjAct_smul_mem_relationSet {r : ℕ} {ζ : ℂ} {g : ℕ}
    (u : ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hx : x ∈ relationSet r ζ g) :
    u • x ∈ relationSet r ζ g := by
  rw [mem_relationSet_iff] at hx ⊢
  let v := ConjAct.ofConjAct u
  let φ : Matrix.specialUnitaryGroup (Fin r) ℂ →* Matrix.specialUnitaryGroup (Fin r) ℂ :=
    (MulAut.conj v).toMonoidHom
  have hlist : (List.ofFn fun j => ⁅((u • x) j).1, ((u • x) j).2⁆) =
      (List.ofFn fun j => ⁅(x j).1, (x j).2⁆).map φ := by
    rw [List.map_ofFn]
    refine congrArg List.ofFn (funext fun j => ?_)
    simp only [Function.comp_def, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd,
      ConjAct.smul_eq_mulAut_conj, φ, v, MulEquiv.coe_toMonoidHom, map_commutatorElement]
  rw [hlist, ← map_list_prod]
  simp only [φ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Submonoid.coe_mul, hx,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.specialUnitaryGroup.coe_mul_coe_inv]

/-- `relationSet r ζ g` as an invariant subset (`SubMulAction`) under simultaneous conjugation by
`ConjAct (SU(r))`. -/
def relationSubMulAction (r : ℕ) (ζ : ℂ) (g : ℕ) :
    SubMulAction (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
      (Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) where
  carrier := relationSet r ζ g
  smul_mem' u _ hx := conjAct_smul_mem_relationSet u hx

/-- Membership in `relationSubMulAction r ζ g` coincides with membership in `relationSet r ζ g`. -/
@[simp]
theorem mem_relationSubMulAction_iff {r : ℕ} {ζ : ℂ} {g : ℕ}
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ} :
    x ∈ relationSubMulAction r ζ g ↔ x ∈ relationSet r ζ g :=
  (Iff.rfl)

/-- Simultaneous conjugation action of `ConjAct (SU(r))` directly on `relationSet r ζ g`. -/
noncomputable instance instMulActionConjActRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    MulAction (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationSet r ζ g) :=
  inferInstanceAs (MulAction (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
    (relationSubMulAction r ζ g))

/-- Coercing `u • x` from `relationSet r ζ g` to the ambient tuple type agrees with `u • x.1`. -/
@[simp]
theorem conjAct_smul_relationSet_coe {r : ℕ} {ζ : ℂ} {g : ℕ}
    (u : ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ)) (x : relationSet r ζ g) :
    ((u • x : relationSet r ζ g) :
      Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) =
      u • x.1 :=
  (rfl)

/-- Each element of `ConjAct (SU(r))` acts continuously on `relationSet r ζ g`. -/
instance instContinuousConstSMulConjActRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    ContinuousConstSMul (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
      (relationSet r ζ g) :=
  inferInstanceAs (ContinuousConstSMul (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
    (relationSubMulAction r ζ g))

/-- The conjugation moduli `R_g / SU(r)` of the twisted `SU(r)` surface relation: the quotient of
`relationSet r ζ g` by the pullback of the simultaneous conjugation orbit relation, endowed with
the quotient topology. -/
abbrev relationModuli (r : ℕ) (ζ : ℂ) (g : ℕ) : Type :=
  Quotient ((MulAction.orbitRel (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
    (Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ)).comap
    (Subtype.val : relationSet r ζ g → _))

/-- The quotient projection from `relationSet r ζ g` onto `relationModuli r ζ g`. -/
def relationModuliMk {r : ℕ} {ζ : ℂ} {g : ℕ} (x : relationSet r ζ g) :
    relationModuli r ζ g :=
  Quotient.mk _ x

/-- The quotient projection `relationModuliMk` is surjective. -/
theorem relationModuliMk_surjective (r : ℕ) (ζ : ℂ) (g : ℕ) :
    Function.Surjective (@relationModuliMk r ζ g) :=
  Quotient.mk_surjective

/-- The quotient projection `relationModuliMk` is continuous. -/
theorem continuous_relationModuliMk (r : ℕ) (ζ : ℂ) (g : ℕ) :
    Continuous (@relationModuliMk r ζ g) :=
  continuous_quot_mk

/-- The quotient projection `relationModuliMk` is a topological quotient map. -/
theorem isQuotientMap_relationModuliMk (r : ℕ) (ζ : ℂ) (g : ℕ) :
    IsQuotientMap (@relationModuliMk r ζ g) :=
  isQuotientMap_quot_mk

/-- Two points of `relationSet r ζ g` represent the same class in `relationModuli r ζ g` precisely
when one is carried to the other by simultaneous conjugation by an element of `SU(r)`. -/
@[simp]
theorem relationModuliMk_eq_iff {r : ℕ} {ζ : ℂ} {g : ℕ} (x y : relationSet r ζ g) :
    relationModuliMk x = relationModuliMk y ↔
      ∃ u : Matrix.specialUnitaryGroup (Fin r) ℂ, ConjAct.toConjAct u • y.1 = x.1 := by
  rw [relationModuliMk, relationModuliMk, Quotient.eq, Setoid.comap_rel,
    MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ConjAct.toConjAct.toEquiv.exists_congr_left

/-- Simultaneous conjugation by `ConjAct (SU(r))` acts trivially on `relationModuli r ζ g`. -/
@[simp]
theorem relationModuliMk_conjAct_smul {r : ℕ} {ζ : ℂ} {g : ℕ}
    (u : ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ)) (x : relationSet r ζ g) :
    relationModuliMk (u • x) = relationModuliMk x :=
  (relationModuliMk_eq_iff (u • x) x).mpr ⟨ConjAct.ofConjAct u, by simp⟩

/-- Homeomorphism identifying `relationModuli r ζ g` with the `MulAction.orbitRel.Quotient` of
`ConjAct (SU(r))` acting directly on `relationSet r ζ g`. -/
noncomputable def relationModuliHomeomorphOrbitQuotient (r : ℕ) (ζ : ℂ) (g : ℕ) :
    relationModuli r ζ g ≃ₜ
      MulAction.orbitRel.Quotient (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
        (relationSet r ζ g) :=
  Homeomorph.Quotient.congrRight
    (Setoid.ext_iff.mp (SubMulAction.orbitRel_of_subMul (relationSubMulAction r ζ g)).symm)

/-- `relationModuliHomeomorphOrbitQuotient` sends `relationModuliMk x` to `Quotient.mk _ x`. -/
@[simp]
theorem relationModuliHomeomorphOrbitQuotient_mk {r : ℕ} {ζ : ℂ} {g : ℕ}
    (x : relationSet r ζ g) :
    relationModuliHomeomorphOrbitQuotient r ζ g (relationModuliMk x) = Quotient.mk _ x :=
  (rfl)

/-- The quotient projection `relationModuliMk` is an open quotient map, since `ConjAct (SU(r))`
acts by homeomorphisms on `relationSet r ζ g`. -/
theorem isOpenQuotientMap_relationModuliMk (r : ℕ) (ζ : ℂ) (g : ℕ) :
    IsOpenQuotientMap (@relationModuliMk r ζ g) := by
  have hcomp : (relationModuliHomeomorphOrbitQuotient r ζ g).symm ∘
      (Quotient.mk _ : relationSet r ζ g →
        MulAction.orbitRel.Quotient (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
          (relationSet r ζ g)) = @relationModuliMk r ζ g :=
    funext fun x => by
      rw [Function.comp_apply, ← relationModuliHomeomorphOrbitQuotient_mk,
        Homeomorph.symm_apply_apply]
  rw [← hcomp]
  exact (relationModuliHomeomorphOrbitQuotient r ζ g).symm.isOpenQuotientMap.comp
    MulAction.isOpenQuotientMap_quotientMk

/-! ### Compactness and Hausdorffness -/

/-- Continuity of the ordered commutator-product map from `Fin g → SU(r) × SU(r)` into
`Matrix (Fin r) (Fin r) ℂ`. -/
private theorem continuous_commutatorProd (r g : ℕ) :
    Continuous (fun x : Fin g →
        Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ =>
      ((List.ofFn fun j => ⁅(x j).1, (x j).2⁆).prod : Matrix (Fin r) (Fin r) ℂ)) := by
  refine continuous_subtype_val.comp ?_
  induction g with
  | zero =>
    simpa only [List.ofFn_zero, List.prod_nil] using continuous_const
  | succ g ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    have hhead : Continuous (fun x : Fin (g + 1) →
          Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ =>
        ⁅(x 0).1, (x 0).2⁆) := by
      simp only [commutatorElement_def]
      fun_prop
    have htail : Continuous (fun x : Fin (g + 1) →
          Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ =>
        (List.ofFn fun j : Fin g => ⁅(x j.succ).1, (x j.succ).2⁆).prod) :=
      ih.comp (continuous_pi fun j => continuous_apply j.succ)
    exact hhead.mul htail

/-- `relationSet r ζ g` is a closed subset of `Fin g → SU(r) × SU(r)`. -/
theorem isClosed_relationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    IsClosed (relationSet r ζ g) :=
  isClosed_singleton.preimage (continuous_commutatorProd r g)

/-- `relationSet r ζ g` is a compact subset of `Fin g → SU(r) × SU(r)`: it is closed in a finite
product of copies of the compact group `SU(r)`. -/
theorem isCompact_relationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    IsCompact (relationSet r ζ g) :=
  IsCompact.of_isClosed_subset isCompact_univ (isClosed_relationSet r ζ g) (Set.subset_univ _)

/-- `relationSet r ζ g` is a compact topological space. -/
instance instCompactSpaceRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    CompactSpace (relationSet r ζ g) :=
  isCompact_iff_compactSpace.mp (isCompact_relationSet r ζ g)

/-- `relationModuli r ζ g` is compact, as a quotient of the compact space `relationSet r ζ g`. -/
instance instCompactSpaceRelationModuli (r : ℕ) (ζ : ℂ) (g : ℕ) :
    CompactSpace (relationModuli r ζ g) :=
  Quotient.compactSpace

/-- `relationModuli r ζ g` is Hausdorff: `relationModuliMk` is an open quotient map and the orbit
relation is the image of the compact space `SU(r) × relationSet r ζ g`, hence closed. -/
instance instT2SpaceRelationModuli (r : ℕ) (ζ : ℂ) (g : ℕ) :
    T2Space (relationModuli r ζ g) := by
  rw [t2Space_iff_of_isOpenQuotientMap (isOpenQuotientMap_relationModuliMk r ζ g)]
  let Φ : Matrix.specialUnitaryGroup (Fin r) ℂ × relationSet r ζ g →
      relationSet r ζ g × relationSet r ζ g :=
    fun p => (ConjAct.toConjAct p.1 • p.2, p.2)
  have hcont : Continuous Φ := by
    refine Continuous.prodMk (continuous_induced_rng.2 ?_) continuous_snd
    have hact : Continuous fun p : Matrix.specialUnitaryGroup (Fin r) ℂ ×
        (Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) =>
        ConjAct.toConjAct p.1 • p.2 :=
      continuous_pi fun j => by
        simp only [Pi.smul_apply, Prod.smul_def, ConjAct.toConjAct_smul]
        fun_prop
    simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq,
      conjAct_smul_relationSet_coe] using
      hact.comp (continuous_id.prodMap continuous_subtype_val)
  have hrange : {q : relationSet r ζ g × relationSet r ζ g |
      relationModuliMk q.1 = relationModuliMk q.2} = Set.range Φ := by
    ext ⟨a, b⟩
    simp only [Set.mem_ofPred_eq, relationModuliMk_eq_iff, Set.mem_range, Prod.ext_iff, Φ]
    refine ⟨fun ⟨u, hu⟩ => ⟨(u, b), Subtype.ext hu, rfl⟩,
      fun ⟨⟨u, b'⟩, ha, hb⟩ => ?_⟩
    subst hb
    exact ⟨u, congrArg Subtype.val ha⟩
  rw [hrange]
  exact (isCompact_range hcont).isClosed

/-! ### Centrality of stabilizers and the free `PSU(r)` action -/

/-- If `ζ ^ card {i : Fin r // d i = d i₀} = 1` for a primitive `r`-th root of unity `ζ`, then `d`
is constant on `Fin r`. -/
private theorem eq_const_of_pow_card_subtype_eq_one {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    {d : Fin r → ℂ} (i₀ : Fin r)
    (hpow : ζ ^ Fintype.card {i : Fin r // d i = d i₀} = 1) :
    ∀ i : Fin r, d i = d i₀ := by
  let S := {i : Fin r // d i = d i₀}
  have hpos : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨⟨i₀, rfl⟩⟩
  have hle : Fintype.card S ≤ r := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun i : Fin r => d i = d i₀)
  have hcard : Fintype.card S = r :=
    le_antisymm hle (Nat.le_of_dvd hpos (hζ.dvd_of_pow_eq_one _ hpow))
  have huniv : Finset.univ.filter (fun i : Fin r => d i = d i₀) = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa [S, Fintype.card_subtype] using hcard)
  intro i
  have hi : i ∈ Finset.univ.filter (fun k : Fin r => d k = d i₀) :=
    huniv.symm ▸ Finset.mem_univ i
  simpa using hi

/-- If `w * u * w⁻¹` has underlying matrix `diagonal d`, then any `y ∈ SU(r)` commuting with `u`
conjugates to a matrix commuting with `diagonal d`. -/
private theorem commute_diagonal_conj_of_commute {r : ℕ} {d : Fin r → ℂ}
    {u w y : Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hw : ((w * u * w⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      diagonal d)
    (hy : Commute u y) :
    Commute (diagonal d)
      ((w * y * w⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
  have hc : Commute (w * u * w⁻¹) (w * y * w⁻¹) := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      hy.map (MulAut.conj w).toMonoidHom
  dsimp only [Commute, SemiconjBy]
  rw [← hw, ← Submonoid.coe_mul, ← Submonoid.coe_mul]
  exact congrArg Subtype.val hc.eq

/-- If every entry of a tuple `x : Fin g → SU(r) × SU(r)` commutes with `diagonal d`, then the
ordered commutator product of `x` has determinant `1` on the eigenblock `{i // d i = d i₀}`. -/
private theorem det_submatrix_commutatorProd_eq_one {r g : ℕ} {d : Fin r → ℂ} (i₀ : Fin r)
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hcomm : ∀ j, Commute (diagonal d) ((x j).1 : Matrix (Fin r) (Fin r) ℂ) ∧
      Commute (diagonal d) ((x j).2 : Matrix (Fin r) (Fin r) ℂ)) :
    ((((List.ofFn fun j => ⁅(x j).1, (x j).2⁆).prod :
        Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).submatrix
      (Subtype.val : {i : Fin r // d i = d i₀} → Fin r)
      (Subtype.val : {i : Fin r // d i = d i₀} → Fin r)).det = 1 := by
  let toMat : Matrix.specialUnitaryGroup (Fin r) ℂ →* Matrix (Fin r) (Fin r) ℂ :=
    (Matrix.specialUnitaryGroup (Fin r) ℂ).subtype
  have hunit : ∀ a b : Matrix.specialUnitaryGroup (Fin r) ℂ,
      toMat ⁅a, b⁆ = ((⁅toMat.toHomUnits a, toMat.toHomUnits b⁆ :
        (Matrix (Fin r) (Fin r) ℂ)ˣ) : Matrix (Fin r) (Fin r) ℂ) := fun a b => by
    rw [← map_commutatorElement, MonoidHom.coe_toHomUnits]
  have hcomm_list : ∀ M ∈ (List.ofFn fun j => ⁅(x j).1, (x j).2⁆).map toMat,
      Commute (diagonal d) M := by
    rintro M hM
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hM
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
    have h1 : Commute (diagonal d) ((toMat.toHomUnits (x j).1 : (Matrix (Fin r) (Fin r) ℂ)ˣ) :
        Matrix (Fin r) (Fin r) ℂ) := (hcomm j).1
    have h2 : Commute (diagonal d) ((toMat.toHomUnits (x j).2 : (Matrix (Fin r) (Fin r) ℂ)ˣ) :
        Matrix (Fin r) (Fin r) ℂ) := (hcomm j).2
    rw [hunit, commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul]
    exact ((h1.mul_right h2).mul_right h1.units_inv_right).mul_right h2.units_inv_right
  rw [← Submonoid.coe_subtype (Matrix.specialUnitaryGroup (Fin r) ℂ), map_list_prod,
    det_submatrix_list_prod_of_commute_diagonal _ hcomm_list]
  refine List.prod_eq_one fun a ha => ?_
  obtain ⟨M, hM, rfl⟩ := List.mem_map.mp ha
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hM
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
  rw [hunit]
  exact det_submatrix_commutatorElement_of_commute_diagonal (hcomm j).1 (hcomm j).2

/-- **Centrality of stabilizers on `relationSet`.** When `ζ` is a primitive `r`-th root of unity,
every `u ∈ SU(r)` commuting with all entries of a solution `x ∈ relationSet r ζ g` lies in the
center of `SU(r)`. No positivity assumption on `r` or `g` is needed: for `r = 0`, `SU(0)` is
trivial, while for `g = 0` and `r ≥ 2`, `relationSet r ζ 0` is empty. -/
theorem relationSet_stabilizer_central {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r) {g : ℕ}
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hx : x ∈ relationSet r ζ g) {u : Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hu : ∀ j, Commute u (x j).1 ∧ Commute u (x j).2) :
    u ∈ Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact Subsingleton.elim u 1 ▸ Subgroup.one_mem _
  -- Diagonalize `u` inside `SU(r)` and transport `x` by the same conjugation.
  obtain ⟨w, z, hw⟩ := Matrix.specialUnitaryGroup.exists_conj_eq_diagonal u
  let u' : Matrix.specialUnitaryGroup (Fin r) ℂ := w * u * w⁻¹
  let x' := ConjAct.toConjAct w • x
  let d : Fin r → ℂ := fun i => (z i : ℂ)
  have hcomm_x' : ∀ j, Commute (diagonal d) ((x' j).1 : Matrix (Fin r) (Fin r) ℂ) ∧
      Commute (diagonal d) ((x' j).2 : Matrix (Fin r) (Fin r) ℂ) := fun j =>
    ⟨by simpa only [x', Pi.smul_apply, Prod.smul_fst, ConjAct.toConjAct_smul] using
        commute_diagonal_conj_of_commute hw (hu j).1,
     by simpa only [x', Pi.smul_apply, Prod.smul_snd, ConjAct.toConjAct_smul] using
        commute_diagonal_conj_of_commute hw (hu j).2⟩
  -- Restrict the commutator relation for `x'` to the eigenblock `{i // d i = d i₀}`.
  let i₀ : Fin r := ⟨0, hr⟩
  have hdet1 := det_submatrix_commutatorProd_eq_one i₀ hcomm_x'
  have hx' : x' ∈ relationSet r ζ g := conjAct_smul_mem_relationSet (ConjAct.toConjAct w) hx
  rw [mem_relationSet_iff.mp hx', submatrix_smul, Pi.smul_apply, Pi.smul_apply,
    submatrix_one _ Subtype.val_injective, det_smul, det_one, mul_one] at hdet1
  -- Primitivity of `ζ` forces the eigenblock to be all of `Fin r`, so `u'` is scalar (central).
  have hu'_center : u' ∈ Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) :=
    Matrix.specialUnitaryGroup.mem_center_of_coe_eq_scalar
      (by rw [hw, scalar_apply]; exact congrArg diagonal (funext
        (eq_const_of_pow_card_subtype_eq_one hζ i₀ hdet1)))
  -- Conjugate back from `u' = w * u * w⁻¹` to `u`.
  have hu_eq : u = w⁻¹ * u' * w := by simp [u', mul_assoc]
  rw [hu_eq, Subgroup.mem_center_iff.mp hu'_center w⁻¹, inv_mul_cancel_right]
  exact hu'_center

/-- Simultaneous conjugation of a family of pairs by a central element is trivial. -/
private theorem toConjAct_smul_eq_self_of_mem_center {G ι : Type*} [Group G] {u : G}
    (hu : u ∈ Subgroup.center G) (x : ι → G × G) :
    ConjAct.toConjAct u • x = x :=
  funext fun j => Prod.ext
    (by rw [Pi.smul_apply, Prod.smul_fst, ConjAct.toConjAct_smul_eq_self_of_mem_center hu])
    (by rw [Pi.smul_apply, Prod.smul_snd, ConjAct.toConjAct_smul_eq_self_of_mem_center hu])

/-- **Exact conjugation stabilizers on `relationSet`.** When `IsPrimitiveRoot ζ r`, an element of
`SU(r)` fixes `x ∈ relationSet r ζ g` under simultaneous conjugation if and only if it lies in the
center of `SU(r)`. -/
theorem conjAct_toConjAct_smul_eq_self_iff_mem_center {r : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) {g : ℕ}
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hx : x ∈ relationSet r ζ g) (u : Matrix.specialUnitaryGroup (Fin r) ℂ) :
    ConjAct.toConjAct u • x = x ↔
      u ∈ Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) := by
  refine ⟨fun h => relationSet_stabilizer_central hζ hx fun j => ?_,
    fun hu => toConjAct_smul_eq_self_of_mem_center hu x⟩
  have hj1 := congrArg Prod.fst (congrFun h j)
  have hj2 := congrArg Prod.snd (congrFun h j)
  simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, ConjAct.toConjAct_smul,
    mul_inv_eq_iff_eq_mul] at hj1 hj2
  exact ⟨hj1, hj2⟩

/-- Simultaneous conjugation by `SU(r)` descends to an action of the projective quotient
`SU(r) ⧸ Subgroup.center (SU(r))` on `relationSet r ζ g`. -/
noncomputable instance instMulActionQuotientCenterRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    MulAction (Matrix.specialUnitaryGroup (Fin r) ℂ ⧸
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationSet r ζ g) :=
  let φ : Matrix.specialUnitaryGroup (Fin r) ℂ →* Equiv.Perm (relationSet r ζ g) :=
    (MulAction.toPermHom (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
      (relationSet r ζ g)).comp ConjAct.toConjAct.toMonoidHom
  MulAction.compHom (relationSet r ζ g) <|
    QuotientGroup.lift (Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) φ fun u hu => by
      ext x : 2
      simp only [φ, MonoidHom.comp_apply, MulAction.toPermHom_apply, MulAction.toPerm_apply,
        MulEquiv.coe_toMonoidHom, Equiv.Perm.coe_one, id_eq, conjAct_smul_relationSet_coe]
      exact toConjAct_smul_eq_self_of_mem_center hu x.1

/-- A coset `QuotientGroup.mk u` in `SU(r) ⧸ center(SU(r))` acts on `relationSet r ζ g` by
simultaneous conjugation by `u`. -/
@[simp]
theorem quotientCenter_mk_smul_coe {r : ℕ} {ζ : ℂ} {g : ℕ}
    (u : Matrix.specialUnitaryGroup (Fin r) ℂ) (x : relationSet r ζ g) :
    (((QuotientGroup.mk u : Matrix.specialUnitaryGroup (Fin r) ℂ ⧸
        Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) • x : relationSet r ζ g) :
      Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) =
      ConjAct.toConjAct u • x.1 :=
  (rfl)

/-- **Freeness of the effective `PSU(r)` action on `relationSet`.** When `IsPrimitiveRoot ζ r`, the
descended action of `SU(r) ⧸ Subgroup.center (SU(r))` on `relationSet r ζ g` is cancellative
(free). -/
theorem isCancelSMul_quotientCenter_relationSet {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    (g : ℕ) :
    IsCancelSMul (Matrix.specialUnitaryGroup (Fin r) ℂ ⧸
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationSet r ζ g) where
  right_cancel' q₁ q₂ x h := by
    obtain ⟨u₁, rfl⟩ := QuotientGroup.mk_surjective q₁
    obtain ⟨u₂, rfl⟩ := QuotientGroup.mk_surjective q₂
    apply QuotientGroup.eq.mpr
    have hfix : ConjAct.toConjAct (u₁⁻¹ * u₂) • x.1 = x.1 := by
      rw [map_mul, mul_smul, map_inv, inv_smul_eq_iff]
      simpa only [quotientCenter_mk_smul_coe] using (congrArg Subtype.val h).symm
    exact (conjAct_toConjAct_smul_eq_self_iff_mem_center hζ x.2 (u₁⁻¹ * u₂)).mp hfix

/-- Homeomorphism identifying `relationModuli r ζ g` with the orbit quotient of the effective
`SU(r) ⧸ Subgroup.center (SU(r))` action on `relationSet r ζ g`. -/
noncomputable def relationModuliHomeomorphQuotientCenter (r : ℕ) (ζ : ℂ) (g : ℕ) :
    relationModuli r ζ g ≃ₜ
      MulAction.orbitRel.Quotient
        (Matrix.specialUnitaryGroup (Fin r) ℂ ⧸
          Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
        (relationSet r ζ g) :=
  Homeomorph.Quotient.congrRight fun x y => by
    rw [Setoid.comap_rel]
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff,
      QuotientGroup.mk_surjective.exists, Subtype.ext_iff, quotientCenter_mk_smul_coe]
    exact ConjAct.toConjAct.toEquiv.exists_congr_left

/-- `relationModuliHomeomorphQuotientCenter` sends `relationModuliMk x` to `Quotient.mk _ x`. -/
@[simp]
theorem relationModuliHomeomorphQuotientCenter_mk {r : ℕ} {ζ : ℂ} {g : ℕ}
    (x : relationSet r ζ g) :
    relationModuliHomeomorphQuotientCenter r ζ g (relationModuliMk x) = Quotient.mk _ x :=
  (rfl)

/-! ### Sphere emptiness, low rank, and central holonomy twists -/

/-- On the sphere (`g = 0`), `relationSet r ζ 0` is empty whenever `1 ≤ r` and `ζ ≠ 1`. -/
theorem isEmpty_relationSet_zero {r : ℕ} (hr : 1 ≤ r) {ζ : ℂ} (hζ : ζ ≠ 1) :
    IsEmpty (relationSet r ζ 0) :=
  ⟨fun ⟨_, hx⟩ => hζ <| by
    have h := congr_fun₂ (mem_relationSet_zero_iff.mp hx) ⟨0, hr⟩ ⟨0, hr⟩
    simpa using h.symm⟩

/-- On the sphere (`g = 0`), `relationModuli r ζ 0` is empty whenever `1 ≤ r` and `ζ ≠ 1`. -/
theorem isEmpty_relationModuli_zero {r : ℕ} (hr : 1 ≤ r) {ζ : ℂ} (hζ : ζ ≠ 1) :
    IsEmpty (relationModuli r ζ 0) :=
  ⟨fun q => (isEmpty_relationSet_zero hr hζ).false q.out⟩

/-- On the sphere (`g = 0`), `relationModuli r ζ 0` is empty whenever `2 ≤ r` and
`IsPrimitiveRoot ζ r`. -/
theorem isEmpty_relationModuli_zero_of_isPrimitiveRoot {r : ℕ} (hr : 2 ≤ r) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) :
    IsEmpty (relationModuli r ζ 0) :=
  isEmpty_relationModuli_zero (by omega) (hζ.ne_one hr)

/-- For `r ≤ 1`, `SU(r)` is a subsingleton, so `relationModuli r ζ g` is a subsingleton for every
`ζ` and every genus `g`. -/
theorem subsingleton_relationModuli_of_le_one {r : ℕ} (hr : r ≤ 1) (ζ : ℂ) (g : ℕ) :
    Subsingleton (relationModuli r ζ g) := by
  have : Subsingleton (Fin r) := ⟨fun a b => Fin.ext (by omega)⟩
  infer_instance

/-- At `ζ = 1`, the trivial tuple `(1, 1, …, 1, 1)` lies in `relationSet r 1 g` for all `r` and
`g`. -/
instance instNonemptyRelationSetUntwisted (r g : ℕ) :
    Nonempty (relationSet r 1 g) :=
  ⟨⟨fun _ => (1, 1), by simp [mem_relationSet_iff, List.ofFn_const]⟩⟩

/-- At `ζ = 1`, `relationModuli r 1 g` is nonempty for all `r` and `g`. -/
instance instNonemptyRelationModuliUntwisted (r g : ℕ) :
    Nonempty (relationModuli r 1 g) :=
  ⟨relationModuliMk (Classical.arbitrary (relationSet r 1 g))⟩

/-- For `r ≤ 1`, `relationModuli r 1 g` is simply connected for every genus `g`. -/
theorem simplyConnectedSpace_relationModuli_of_le_one {r : ℕ} (hr : r ≤ 1) (g : ℕ) :
    SimplyConnectedSpace (relationModuli r 1 g) := by
  have : Subsingleton (relationModuli r 1 g) := subsingleton_relationModuli_of_le_one hr 1 g
  infer_instance

/-- Entrywise multiplication by pairs of central elements of `SU(r)` preserves `relationSet r ζ g`:
central scalars cancel in every commutator `⁅c₁ * A, c₂ * B⁆ = ⁅A, B⁆`. -/
theorem centerTwist_mem_relationSet {r : ℕ} {ζ : ℂ} {g : ℕ}
    (ε : Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hx : x ∈ relationSet r ζ g) :
    (fun j => (((ε j).1 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (x j).1,
      ((ε j).2 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (x j).2)) ∈ relationSet r ζ g := by
  rw [mem_relationSet_iff] at hx ⊢
  have hcomm_eq : ∀ j : Fin g,
      ⁅((ε j).1 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (x j).1,
        ((ε j).2 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (x j).2⁆ =
      ⁅(x j).1, (x j).2⁆ := fun j => by
    rw [← Subgroup.mem_center_iff.mp (ε j).1.2 (x j).1,
      ← Subgroup.mem_center_iff.mp (ε j).2.2 (x j).2]
    exact TauCeti.commutatorElement_mul_mul_of_mem_center (ε j).1.2 (ε j).2.2
  simpa only [hcomm_eq] using hx

/-- Scalar multiplication of central holonomy twists `Fin g → center(SU(r)) × center(SU(r))` on
`relationSet r ζ g` by entrywise multiplication. -/
noncomputable instance instSMulCenterTwistRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    SMul (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationSet r ζ g) where
  smul ε x := ⟨fun j => (((ε j).1 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (x.1 j).1,
      ((ε j).2 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (x.1 j).2),
    centerTwist_mem_relationSet ε x.2⟩

/-- Coercing a central twist `ε • x` from `relationSet r ζ g` multiplies each pair `(A_j, B_j)`
entrywise by `((ε j).1, (ε j).2)`. -/
@[simp]
theorem centerTwist_smul_relationSet_coe {r : ℕ} {ζ : ℂ} {g : ℕ}
    (ε : Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (x : relationSet r ζ g) :
    ((ε • x : relationSet r ζ g) :
      Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) =
      fun j => (((ε j).1 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (x.1 j).1,
        ((ε j).2 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (x.1 j).2) :=
  (rfl)

/-- The group `Fin g → center(SU(r)) × center(SU(r))` of central holonomy twists acts on
`relationSet r ζ g` by entrywise multiplication. -/
noncomputable instance instMulActionCenterTwistRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    MulAction (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationSet r ζ g) where
  one_smul x := Subtype.ext <| by simp [centerTwist_smul_relationSet_coe]
  mul_smul ε₁ ε₂ x := Subtype.ext <| by simp [centerTwist_smul_relationSet_coe, mul_assoc]

/-- The central holonomy twist action on `relationSet r ζ g` is jointly continuous. -/
instance instContinuousSMulCenterTwistRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    ContinuousSMul (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationSet r ζ g) where
  continuous_smul := continuous_induced_rng.2 <| by
    simp only [Function.comp_def, centerTwist_smul_relationSet_coe]
    have hact : Continuous fun p : (Fin g →
        Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
        Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) ×
        (Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) =>
        fun j => (((p.1 j).1 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (p.2 j).1,
          ((p.1 j).2 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (p.2 j).2) :=
      continuous_pi fun j => by fun_prop
    exact hact.comp (continuous_id.prodMap continuous_subtype_val)

/-- Entrywise central twisting commutes with simultaneous `SU(r)`-conjugation, so it descends to a
group action on `relationModuli r ζ g`. -/
noncomputable instance instMulActionCenterTwistRelationModuli (r : ℕ) (ζ : ℂ) (g : ℕ) :
    MulAction (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationModuli r ζ g) where
  smul ε := Quotient.map' (ε • ·) fun x y ⟨u, hu⟩ => ⟨u, by
    dsimp only at hu ⊢
    rw [centerTwist_smul_relationSet_coe, centerTwist_smul_relationSet_coe]
    funext j
    have hj1 : u • (y.1 j).1 = (x.1 j).1 := by
      simpa only [Pi.smul_apply, Prod.smul_fst] using congrArg Prod.fst (congrFun hu j)
    have hj2 : u • (y.1 j).2 = (x.1 j).2 := by
      simpa only [Pi.smul_apply, Prod.smul_snd] using congrArg Prod.snd (congrFun hu j)
    exact Prod.ext
      (by rw [Pi.smul_apply, Prod.smul_fst, ConjAct.smul_mul_of_mem_center u (ε j).1.2, hj1])
      (by rw [Pi.smul_apply, Prod.smul_snd, ConjAct.smul_mul_of_mem_center u (ε j).2.2, hj2])⟩
  one_smul q := Quotient.inductionOn' q fun x => congrArg Quotient.mk'' (one_smul _ x)
  mul_smul ε₁ ε₂ q :=
    Quotient.inductionOn' q fun x => congrArg Quotient.mk'' (mul_smul ε₁ ε₂ x)

/-- The quotient projection `relationModuliMk` is equivariant for central holonomy twists. -/
@[simp]
theorem centerTwist_smul_relationModuliMk {r : ℕ} {ζ : ℂ} {g : ℕ}
    (ε : Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (x : relationSet r ζ g) :
    ε • relationModuliMk x = relationModuliMk (ε • x) :=
  (rfl)

/-- The descended central holonomy twist action on `relationModuli r ζ g` is jointly continuous. -/
instance instContinuousSMulCenterTwistRelationModuli (r : ℕ) (ζ : ℂ) (g : ℕ) :
    ContinuousSMul (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationModuli r ζ g) where
  continuous_smul := by
    have hq : IsQuotientMap (Prod.map
        (id : (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
          Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) → _)
        (@relationModuliMk r ζ g)) :=
      (IsOpenQuotientMap.id.prodMap (isOpenQuotientMap_relationModuliMk r ζ g)).isQuotientMap
    rw [hq.continuous_iff]
    have hcomp : (fun p => p.1 • p.2) ∘ Prod.map
          (id : (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
            Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) → _)
          (@relationModuliMk r ζ g) =
        (@relationModuliMk r ζ g) ∘ (fun p => p.1 • p.2) :=
      funext fun ⟨ε, x⟩ => centerTwist_smul_relationModuliMk ε x
    rw [hcomp]
    exact (continuous_relationModuliMk r ζ g).comp continuous_smul

end TauCeti.SpecialUnitary
