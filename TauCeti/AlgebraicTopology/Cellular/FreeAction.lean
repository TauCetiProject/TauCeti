/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.RepresentationTheory.Rep.Iso
public import TauCeti.AlgebraicTopology.Cellular.Equivariant
public import TauCeti.AlgebraicTopology.Cellular.LocalDegree
public import TauCeti.RepresentationTheory.FreeOfBasis
public import TauCeti.Topology.CWComplex.Classical.OrbitSpace
import TauCeti.AlgebraicTopology.Cellular.Permutation

/-!
# Cellular chains of free cellular actions

Let a group `G` act continuously on a Hausdorff space `E` carrying a CW complex `C` so that every
element `g : G` carries each open `n`-cell onto an open `n`-cell (`hcell`). Unlike the lifted CW
structure of a covering (`TauCeti.AlgebraicTopology.Cellular.Covering`), the translations need not
preserve chosen characteristic maps: an element of `G` may permute vertices of a simplicial cell or
reverse the orientation of a cell.

This file shows that on cellular chains with coefficients in a ring `R`, each translation sends the
cellular basis vector of a cell `i` to a unit scalar multiple of the cellular basis vector of the
translated cell `g • i` (`TauCeti.cellActionChainRepresentation_cellularChainBasis` and
`TauCeti.cellActionUnit`). The coordinate of any other `n`-cell `k ≠ g • i` vanishes because the
translate `g • openCell n i = openCell n (g • i)` misses `openCell n k`, while the frontier of `i`
is carried into the `(n - 1)`-skeleton, so the induced map into the local homology
`Hₙ(Xⁿ, Xⁿ ∖ {x})` at `x ∈ openCell n k` factors through the subspace `Xⁿ ∖ {x}`
(`TauCeti.cellularChainBasis_repr_cellularChainGroupMap_eq_zero_of_ne` and
`TauCeti.cellularChainGroupMap_cellularChainBasis_eq_smul`, proved in
`TauCeti.AlgebraicTopology.Cellular.LocalDegree`). Functoriality of cellular chains on `1` and
`g * h` turns these local scalars into units over `R`; they are `1` on `0`-cells and whenever the
translation carries characteristic maps strictly onto characteristic maps
(`TauCeti.cellActionUnit_eq_one_of_smul_map`).

When `G` acts freely on the cells (`hfree`) and `R` is a commutative ring, rescaling the geometric
cellular basis along each orbit by `TauCeti.cellActionUnit` produces an `R`-basis
`TauCeti.cellActionOrbitBasis` that agrees with the cellular basis on a chosen representative `s a`
of each orbit and is permuted without signs by `G`. Consequently:

* each cellular chain group is isomorphic in `Rep R G` to the free representation on the `G`-orbits
  of `n`-cells (`TauCeti.cellActionChainRepIsoFree` and
  `TauCeti.cellActionChainRepIsoFreeOrbitQuotient`), and in particular to the free representation on
  the `n`-cells of the orbit space `B` of a quotient covering map `p : E → B`
  (`TauCeti.quotientCellularChainRepIsoFree`), hence is projective
  (`TauCeti.projective_cellActionChainComplexRep_X`);
* when `C` is contractible, the augmented cellular chain complex of `C` is a projective resolution
  of the trivial representation `Rep.trivial R G R` (`TauCeti.cellActionResolution`).

## Main definitions

* `TauCeti.cellActionChainRepresentation`: the representation of `G` on the `n`-th cellular chain
  group of `C`.
* `TauCeti.cellActionChainComplexRep`: the cellular chain complex of `C` in
  `ChainComplex (Rep R G) ℕ`.
* `TauCeti.cellActionScale` and `TauCeti.cellActionUnit`: the local scalar (and unit, when `G` is a
  group) by which `g` rescales the cellular basis vector of `i` onto that of `g • i`.
* `TauCeti.cellActionOrbitBasis`: the orbit-rescaled `R`-basis freely permuted by `G`.
* `TauCeti.cellActionChainRepIsoFree` and `TauCeti.quotientCellularChainRepIsoFree`: freeness of
  each cellular chain group over `R[G]` on orbit representatives and on the cells of the orbit
  space.
* `TauCeti.cellActionResolution`: the projective resolution of `Rep.trivial R G R` by the cellular
  chains of a contractible free `G`-CW complex.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section I.4, Proposition 4.1, and
  Section II.4.
* T. tom Dieck, *Transformation Groups*, de Gruyter, 1987, Section II.1 and Section II.2.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2.
-/

public section

noncomputable section

open CategoryTheory Set Topology Topology.RelCWComplex
open scoped Pointwise

universe w

namespace TauCeti

section MonoidAction

variable {E : Type w} [TopologicalSpace E] [T2Space E] (C : Set E) [CWComplex C]
  {G : Type w} [Monoid G] [MulAction G E] [ContinuousConstSMul G E]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n), ∃ j : cell C n, g • openCell n i = openCell n j)
  (R : Type w) [Ring R]

/-- The representation of `G` on the `n`-th cellular chain group of `C`, induced by a continuous
monoid action carrying open cells onto open cells of the same dimension. -/
def cellActionChainRepresentation (n : ℕ) :
    Representation R G (cellularChainGroup C (ModuleCat.of R R) n : ModuleCat R) :=
  cellularActionRepresentation C (fun g ↦ cellActionSMul C g (hcell g))
    (fun g ↦ isCellular_cellActionSMul C g (hcell g)) (cellActionSMul_one C (hcell 1))
    (fun g h ↦ cellActionSMul_mul C (hcell g) (hcell h) (hcell (g * h))) R n

/-- An element `g` acts on the cellular chains of `C` by the cellular chain map of translation by
`g`. -/
@[simp]
theorem cellActionChainRepresentation_apply (n : ℕ) (g : G) :
    cellActionChainRepresentation C hcell R n g =
      (cellularChainGroupMap C C (isCellular_cellActionSMul C g (hcell g))
        (ModuleCat.of R R) n).hom := by
  unfold cellActionChainRepresentation
  exact cellularActionRepresentation_apply _ _ _ _ _ _ _ _

/-- The cellular differential of `C` as an equivariant morphism of representations. -/
def cellActionDifferentialRep (n : ℕ) :
    Rep.of (cellActionChainRepresentation C hcell R (n + 1)) ⟶
      Rep.of (cellActionChainRepresentation C hcell R n) :=
  cellularActionDifferential C (fun g ↦ cellActionSMul C g (hcell g))
    (fun g ↦ isCellular_cellActionSMul C g (hcell g)) (cellActionSMul_one C (hcell 1))
    (fun g h ↦ cellActionSMul_mul C (hcell g) (hcell h) (hcell (g * h))) R n

/-- The underlying linear map of `TauCeti.cellActionDifferentialRep` is the cellular differential
of `C`. -/
@[simp]
theorem cellActionDifferentialRep_hom_toLinearMap (n : ℕ) :
    (cellActionDifferentialRep C hcell R n).hom.toLinearMap =
      (cellularDifferential C (ModuleCat.of R R) n).hom := by
  unfold cellActionDifferentialRep
  exact cellularActionDifferential_hom_toLinearMap _ _ _ _ _ _ _

/-- **The cellular chain complex of `C` as a chain complex of representations of `G`.** -/
def cellActionChainComplexRep : ChainComplex (Rep.{w} R G) ℕ :=
  cellularActionComplex C (fun g ↦ cellActionSMul C g (hcell g))
    (fun g ↦ isCellular_cellActionSMul C g (hcell g)) (cellActionSMul_one C (hcell 1))
    (fun g h ↦ cellActionSMul_mul C (hcell g) (hcell h) (hcell (g * h))) R

/-- The degree-`n` term of `TauCeti.cellActionChainComplexRep` is
`TauCeti.cellActionChainRepresentation`. -/
@[simp]
theorem cellActionChainComplexRep_X (n : ℕ) :
    (cellActionChainComplexRep C hcell R).X n =
      Rep.of (cellActionChainRepresentation C hcell R n) := by
  unfold cellActionChainComplexRep cellActionChainRepresentation
  exact cellularActionComplex_X _ _ _ _ _ _ _

/-- The differentials of `TauCeti.cellActionChainComplexRep` are the equivariant cellular
differentials. -/
@[simp]
theorem cellActionChainComplexRep_d (n : ℕ) :
    (cellActionChainComplexRep C hcell R).d (n + 1) n =
      eqToHom (cellActionChainComplexRep_X C hcell R (n + 1)) ≫
        cellActionDifferentialRep C hcell R n ≫
        eqToHom (cellActionChainComplexRep_X C hcell R n).symm := by
  unfold cellActionChainComplexRep cellActionDifferentialRep
  exact cellularActionComplex_d _ _ _ _ _ _ n

/-- **Forgetting the action of `G` on `TauCeti.cellActionChainComplexRep` recovers the cellular
chain complex of `C`.** -/
def cellActionChainComplexRepForget₂Iso :
    ((forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).mapHomologicalComplex _).obj
        (cellActionChainComplexRep C hcell R) ≅
      cellularChainComplex C (ModuleCat.of R R) :=
  (cellularActionComplexForget₂Iso C (fun g ↦ cellActionSMul C g (hcell g))
    (fun g ↦ isCellular_cellActionSMul C g (hcell g)) (cellActionSMul_one C (hcell 1))
    (fun g h ↦ cellActionSMul_mul C (hcell g) (hcell h) (hcell (g * h))) R).symm

/-- Components of `TauCeti.cellActionChainComplexRepForget₂Iso` are the definitional object
transports. -/
@[simp]
theorem cellActionChainComplexRepForget₂Iso_hom_f (n : ℕ) :
    (cellActionChainComplexRepForget₂Iso C hcell R).hom.f n = eqToHom (by
      rw [Functor.mapHomologicalComplex_obj_X, cellularChainComplex_X,
        cellActionChainComplexRep_X]
      rfl) := by
  unfold cellActionChainComplexRepForget₂Iso
  exact cellularActionComplexForget₂Iso_inv_f _ _ _ _ _ _ _

/-- Inverse components of `TauCeti.cellActionChainComplexRepForget₂Iso` are the reverse object
transports. -/
@[simp]
theorem cellActionChainComplexRepForget₂Iso_inv_f (n : ℕ) :
    (cellActionChainComplexRepForget₂Iso C hcell R).inv.f n = eqToHom (by
      rw [Functor.mapHomologicalComplex_obj_X, cellularChainComplex_X,
        cellActionChainComplexRep_X]
      rfl) := by
  unfold cellActionChainComplexRepForget₂Iso
  exact cellularActionComplexForget₂Iso_hom_f _ _ _ _ _ _ _

/-- The local scalar in `R` by which translation by `g` rescales the cellular basis vector of `i`
onto that of `g • i`. -/
def cellActionScale (g : G) {n : ℕ} (i : cell C n) : R :=
  letI := cellMulAction hcell n
  (cellularChainBasis C R n).repr
    (cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n i)) (g • i)

/-- `TauCeti.cellActionScale` is the `(g • i)`-coordinate of the translated cellular basis
vector. -/
theorem cellActionScale_def (g : G) {n : ℕ} (i : cell C n) :
    letI := cellMulAction hcell n
    cellActionScale C hcell R g i =
      (cellularChainBasis C R n).repr
        (cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n i)) (g • i) :=
  (rfl)

/-- **Translation by `g` sends the cellular basis vector of `i` to `cellActionScale` times the
cellular basis vector of `g • i`.** This is not a `simp` lemma because `simp` unfolds
`TauCeti.cellularChainBasis` via `TauCeti.cellularChainBasis_apply` first. -/
theorem cellActionChainRepresentation_cellularChainBasis {n : ℕ} (g : G) (i : cell C n) :
    letI := cellMulAction hcell n
    cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n i) =
      cellActionScale C hcell R g i • cellularChainBasis C R n (g • i) := by
  let := cellMulAction hcell n
  rw [cellActionScale_def, cellActionChainRepresentation_apply]
  refine cellularChainGroupMap_cellularChainBasis_eq_smul C C R
    (isCellular_cellActionSMul C g (hcell g)) fun z hz ↦ Or.inr ?_
  rw [coe_cellActionSMul_apply]
  exact smul_mem_openCell_smul hcell g hz

/-- The identity element acts with scalar `1` on every cell. -/
@[simp]
theorem cellActionScale_one {n : ℕ} (i : cell C n) :
    cellActionScale C hcell R (1 : G) i = 1 := by
  let := cellMulAction hcell n
  rw [cellActionScale_def, map_one, Module.End.one_eq_id, LinearMap.id_apply, one_smul,
    Module.Basis.repr_self, Finsupp.single_eq_same]

/-- The local scalars satisfy the cocycle identity `u (g * h) i = u h i * u g (h • i)`. -/
theorem cellActionScale_mul (g h : G) {n : ℕ} (i : cell C n) :
    letI := cellMulAction hcell n
    cellActionScale C hcell R (g * h) i =
      cellActionScale C hcell R h i * cellActionScale C hcell R g (h • i) := by
  let := cellMulAction hcell n
  have h1 := cellActionChainRepresentation_cellularChainBasis C hcell R (g * h) i
  rw [map_mul, Module.End.mul_eq_comp, LinearMap.comp_apply,
    cellActionChainRepresentation_cellularChainBasis C hcell R h i, map_smul,
    cellActionChainRepresentation_cellularChainBasis C hcell R g (h • i), smul_smul,
    ← mul_smul] at h1
  simpa only [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finsupp.single_eq_same] using
    congrArg (fun v ↦ (cellularChainBasis C R n).repr v ((g * h) • i)) h1.symm

/-- When translation by `g` carries the characteristic map of `i` strictly onto that of an `n`-cell
`j`, as for the lifted CW structure of a covering (`TauCeti.map_smul_cellPreimage`), the local
scalar `TauCeti.cellActionScale` is `1`. -/
theorem cellActionScale_eq_one_of_smul_map {n : ℕ} {g : G} {i j : cell C n}
    (hmap : ∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) 1, g • map n i x = map n j x) :
    cellActionScale C hcell R g i = 1 := by
  let := cellMulAction hcell n
  have hj : j = g • i := by
    have hmem : map n j 0 ∈ openCell n j ∧ map n j 0 ∈ openCell n (g • i) :=
      ⟨map_zero_mem_openCell n j, hmap 0 (Metric.mem_closedBall_self zero_le_one) ▸
        smul_mem_openCell_smul hcell g (map_zero_mem_openCell n i)⟩
    exact eq_of_heq (Sigma.mk.inj_iff.1
      (eq_of_not_disjoint_openCell (not_disjoint_iff.2 ⟨_, hmem.1, hmem.2⟩))).2
  subst hj
  have hstrict : cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n i) =
      cellularChainBasis C R n (g • i) := by
    rw [cellActionChainRepresentation_apply]
    exact cellularChainGroupMap_cellularChainBasis C C
      (isCellular_cellActionSMul C g (hcell g)) R fun x hx hxC ↦
        (coe_cellActionSMul_apply C g (hcell g) ⟨map n i x, hxC⟩).trans (hmap x hx)
  rw [cellActionScale_def, hstrict, Module.Basis.repr_self, Finsupp.single_eq_same]

/-- Every element acts with scalar `1` on the cellular basis vector of a `0`-cell. -/
@[simp]
theorem cellActionScale_zero (g : G) (i : cell C 0) :
    cellActionScale C hcell R g i = 1 := by
  let := cellMulAction hcell 0
  refine cellActionScale_eq_one_of_smul_map C hcell R (j := g • i) fun x _ ↦ ?_
  rw [Subsingleton.elim x 0]
  have hmem := smul_mem_openCell_smul hcell g (map_zero_mem_openCell 0 i)
  rw [openCell_zero_eq_singleton, mem_singleton_iff] at hmem
  exact hmem.trans (congrArg (map 0 (g • i)) (Subsingleton.elim _ _))

end MonoidAction

section GroupAction

variable {E : Type w} [TopologicalSpace E] [T2Space E] (C : Set E) [CWComplex C]
  {G : Type w} [Group G] [MulAction G E] [ContinuousConstSMul G E]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n), ∃ j : cell C n, g • openCell n i = openCell n j)
  (R : Type w) [Ring R]

/-- Right inverse relation for `TauCeti.cellActionScale` under a group action. -/
theorem cellActionScale_mul_inv (g : G) {n : ℕ} (i : cell C n) :
    letI := cellMulAction hcell n
    cellActionScale C hcell R g i * cellActionScale C hcell R g⁻¹ (g • i) = 1 := by
  let := cellMulAction hcell n
  have h := cellActionScale_mul C hcell R g⁻¹ g i
  rwa [inv_mul_cancel, cellActionScale_one, eq_comm] at h

/-- Left inverse relation for `TauCeti.cellActionScale` under a group action. -/
theorem cellActionScale_inv_mul (g : G) {n : ℕ} (i : cell C n) :
    letI := cellMulAction hcell n
    cellActionScale C hcell R g⁻¹ (g • i) * cellActionScale C hcell R g i = 1 := by
  let := cellMulAction hcell n
  have h := cellActionScale_mul C hcell R g g⁻¹ (g • i)
  rwa [mul_inv_cancel, cellActionScale_one, inv_smul_smul, eq_comm] at h

/-- **Each element of a group acting on open cells rescales cellular basis vectors by a unit.** -/
def cellActionUnit (g : G) {n : ℕ} (i : cell C n) : Rˣ :=
  letI := cellMulAction hcell n
  ⟨cellActionScale C hcell R g i, cellActionScale C hcell R g⁻¹ (g • i),
    cellActionScale_mul_inv C hcell R g i, cellActionScale_inv_mul C hcell R g i⟩

/-- The underlying ring element of `TauCeti.cellActionUnit` is `TauCeti.cellActionScale`. -/
@[simp]
theorem val_cellActionUnit (g : G) {n : ℕ} (i : cell C n) :
    (cellActionUnit C hcell R g i : R) = cellActionScale C hcell R g i :=
  (rfl)

/-- The local scalar `TauCeti.cellActionScale` is a unit in `R`. -/
theorem isUnit_cellActionScale (g : G) {n : ℕ} (i : cell C n) :
    IsUnit (cellActionScale C hcell R g i) :=
  (cellActionUnit C hcell R g i).isUnit

/-- The identity element acts with unit `1` on every cell. -/
@[simp]
theorem cellActionUnit_one {n : ℕ} (i : cell C n) :
    cellActionUnit C hcell R (1 : G) i = 1 :=
  Units.ext (cellActionScale_one C hcell R i)

/-- The units `TauCeti.cellActionUnit` satisfy the cocycle identity
`u (g * h) i = u h i * u g (h • i)`. -/
theorem cellActionUnit_mul (g h : G) {n : ℕ} (i : cell C n) :
    letI := cellMulAction hcell n
    cellActionUnit C hcell R (g * h) i =
      cellActionUnit C hcell R h i * cellActionUnit C hcell R g (h • i) :=
  Units.ext (cellActionScale_mul C hcell R g h i)

/-- The inverse of the unit of `g` at `i` is the unit of `g⁻¹` at `g • i`. -/
theorem cellActionUnit_inv (g : G) {n : ℕ} (i : cell C n) :
    letI := cellMulAction hcell n
    (cellActionUnit C hcell R g i)⁻¹ = cellActionUnit C hcell R g⁻¹ (g • i) :=
  Units.ext rfl

/-- When translation by `g` carries the characteristic map of `i` strictly onto that of an `n`-cell
`j`, the unit `TauCeti.cellActionUnit` is `1`. -/
theorem cellActionUnit_eq_one_of_smul_map {n : ℕ} {g : G} {i j : cell C n}
    (hmap : ∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) 1, g • map n i x = map n j x) :
    cellActionUnit C hcell R g i = 1 :=
  Units.ext (cellActionScale_eq_one_of_smul_map C hcell R hmap)

/-- Every element acts with unit `1` on the cellular basis vector of a `0`-cell. -/
@[simp]
theorem cellActionUnit_zero (g : G) (i : cell C 0) :
    cellActionUnit C hcell R g i = 1 :=
  Units.ext (cellActionScale_zero C hcell R g i)

end GroupAction

section Free

variable {E : Type w} [TopologicalSpace E] [T2Space E] (C : Set E) [CWComplex C]
  {G : Type w} [Group G] [MulAction G E] [ContinuousConstSMul G E]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n), ∃ j : cell C n, g • openCell n i = openCell n j)
  (hfree : ∀ (g : G) (n : ℕ) (i : cell C n), g • openCell n i = openCell n i → g = 1)
  (R : Type w) [CommRing R]

section Representatives

variable {n : ℕ} {ι : Type w} (s : ι → cell C n)
  (hs : letI := cellMulAction hcell n
    Function.Bijective (fun a ↦ (Quotient.mk'' (s a) :
      MulAction.orbitRel.Quotient G (cell C n))))

/-- **The orbit-adapted cellular basis** associated with orbit representatives `s`: obtained from
`TauCeti.cellularChainBasis` by rescaling each cell `g • s a` by `TauCeti.cellActionUnit`, so that
the vector of `g • s a` is the image under `g` of the cellular basis vector of `s a`. -/
def cellActionOrbitBasis :
    Module.Basis (cell C n) R (cellularChainGroup C (ModuleCat.of R R) n : ModuleCat R) :=
  (cellularChainBasis C R n).unitsSMul fun c ↦
    cellActionUnit C hcell R ((sigmaSMulCellEquiv hcell hfree s hs).symm c).2
      (s ((sigmaSMulCellEquiv hcell hfree s hs).symm c).1)

/-- On the cell `g • s a` indexed by `⟨a, g⟩`, `TauCeti.cellActionOrbitBasis` is the image under
`g` of the cellular basis vector of `s a`. -/
theorem cellActionOrbitBasis_sigmaSMulCellEquiv (a : ι) (g : G) :
    cellActionOrbitBasis C hcell hfree R s hs (sigmaSMulCellEquiv hcell hfree s hs ⟨a, g⟩) =
      cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n (s a)) := by
  let := cellMulAction hcell n
  unfold cellActionOrbitBasis
  rw [Module.Basis.unitsSMul_apply, Equiv.symm_apply_apply, Units.smul_def, val_cellActionUnit,
    sigmaSMulCellEquiv_apply, cellActionChainRepresentation_cellularChainBasis]

/-- On the translate `g • s a` of an orbit representative, `TauCeti.cellActionOrbitBasis` is the
image under `g` of the cellular basis vector of `s a`. -/
@[simp]
theorem cellActionOrbitBasis_smul_section (a : ι) (g : G) :
    letI := cellMulAction hcell n
    cellActionOrbitBasis C hcell hfree R s hs (g • s a) =
      cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n (s a)) := by
  let := cellMulAction hcell n
  rw [← sigmaSMulCellEquiv_apply hcell hfree s hs ⟨a, g⟩, cellActionOrbitBasis_sigmaSMulCellEquiv]

/-- On each chosen orbit representative `s a`, `TauCeti.cellActionOrbitBasis` agrees with the
geometric cellular basis `TauCeti.cellularChainBasis`. -/
@[simp]
theorem cellActionOrbitBasis_apply_section (a : ι) :
    cellActionOrbitBasis C hcell hfree R s hs (s a) = cellularChainBasis C R n (s a) := by
  let := cellMulAction hcell n
  have h1 : sigmaSMulCellEquiv hcell hfree s hs ⟨a, 1⟩ = s a := by
    rw [sigmaSMulCellEquiv_apply, one_smul]
  conv_lhs => rw [← h1]
  rw [cellActionOrbitBasis_sigmaSMulCellEquiv, map_one, Module.End.one_eq_id, LinearMap.id_apply]

/-- Translation by `g` permutes `TauCeti.cellActionOrbitBasis` along the left `G`-action on the
fibres of `TauCeti.sigmaSMulCellEquiv`, with no orientation sign. -/
theorem cellActionChainRepresentation_cellActionOrbitBasis (g h : G) (a : ι) :
    cellActionChainRepresentation C hcell R n g
        (cellActionOrbitBasis C hcell hfree R s hs (sigmaSMulCellEquiv hcell hfree s hs ⟨a, h⟩)) =
      cellActionOrbitBasis C hcell hfree R s hs
        (sigmaSMulCellEquiv hcell hfree s hs ⟨a, g * h⟩) := by
  rw [cellActionOrbitBasis_sigmaSMulCellEquiv, cellActionOrbitBasis_sigmaSMulCellEquiv,
    map_mul, Module.End.mul_eq_comp, LinearMap.comp_apply]

/-- **The cellular chains of a free cellular action are free over `R[G]`**: given one
representative `s a` in each `G`-orbit of `n`-cells, the `n`-th cellular chain group of `C` is
isomorphic in `Rep R G` to `Rep.free R G ι`, sending the cellular basis vector of `s a` to the
generator `single a (single 1 1)`. -/
def cellActionChainRepIsoFree :
    Rep.of (cellActionChainRepresentation C hcell R n) ≅ Rep.free R G ι :=
  (Rep.mkIso ((cellActionChainRepresentation C hcell R n).freeEquivOfBasis
    (cellActionOrbitBasis C hcell hfree R s hs) (sigmaSMulCellEquiv hcell hfree s hs)
    (cellActionChainRepresentation_cellActionOrbitBasis C hcell hfree R s hs))).symm

/-- The generator `single a (single g 1)` of `Rep.free R G ι` corresponds under
`TauCeti.cellActionChainRepIsoFree` to the `g`-translate of the cellular basis vector of `s a`. -/
@[simp]
theorem cellActionChainRepIsoFree_inv_hom_single (a : ι) (g : G) :
    (cellActionChainRepIsoFree C hcell hfree R s hs).inv.hom
        (Finsupp.single a (MonoidAlgebra.single g 1)) =
      cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n (s a)) := by
  rw [cellActionChainRepIsoFree, Iso.symm_inv, Rep.mkIso_hom_hom_apply]
  exact ((cellActionChainRepresentation C hcell R n).freeEquivOfBasis_single
    (cellActionOrbitBasis C hcell hfree R s hs) (sigmaSMulCellEquiv hcell hfree s hs)
    (cellActionChainRepresentation_cellActionOrbitBasis C hcell hfree R s hs) a g 1).trans
    (by rw [one_smul, cellActionOrbitBasis_sigmaSMulCellEquiv])

/-- The cellular basis vector of each chosen representative `s a` maps to the generator
`single a (single 1 1)` of `Rep.free R G ι`. This is not a `simp` lemma because `simp` unfolds
`TauCeti.cellularChainBasis` via `TauCeti.cellularChainBasis_apply` first. -/
theorem cellActionChainRepIsoFree_hom_hom_cellularChainBasis (a : ι) :
    (cellActionChainRepIsoFree C hcell hfree R s hs).hom.hom (cellularChainBasis C R n (s a)) =
      Finsupp.single a (MonoidAlgebra.single 1 1) := by
  have h1 : cellActionChainRepresentation C hcell R n 1 (cellularChainBasis C R n (s a)) =
      cellularChainBasis C R n (s a) := by
    rw [map_one, Module.End.one_eq_id, LinearMap.id_apply]
  rw [← h1, ← cellActionChainRepIsoFree_inv_hom_single C hcell hfree R s hs, Rep.hom_inv_apply]

/-- The cellular basis vector of a translated representative `g • s a` maps to the generator
`single a (single g u⁻¹)` of `Rep.free R G ι`, where `u` is the unit
`TauCeti.cellActionUnit C hcell R g (s a)` by which `g` rescales the cellular basis vector of
`s a`. -/
theorem cellActionChainRepIsoFree_hom_hom_cellularChainBasis_smul (a : ι) (g : G) :
    letI := cellMulAction hcell n
    (cellActionChainRepIsoFree C hcell hfree R s hs).hom.hom
        (cellularChainBasis C R n (g • s a)) =
      Finsupp.single a (MonoidAlgebra.single g (↑(cellActionUnit C hcell R g (s a))⁻¹ : R)) := by
  let := cellMulAction hcell n
  have h := cellActionChainRepIsoFree_inv_hom_single C hcell hfree R s hs a g
  rw [cellActionChainRepresentation_cellularChainBasis, ← val_cellActionUnit] at h
  have hb : cellularChainBasis C R n (g • s a) =
      (↑(cellActionUnit C hcell R g (s a))⁻¹ : R) •
        (cellActionChainRepIsoFree C hcell hfree R s hs).inv.hom
          (Finsupp.single a (MonoidAlgebra.single g 1)) := by
    rw [h, smul_smul, Units.inv_mul, one_smul]
  rw [hb, map_smul, Rep.hom_inv_apply, Finsupp.smul_single, MonoidAlgebra.smul_single', mul_one]

end Representatives

/-- Canonical isomorphism of the `n`-th cellular chain group of a free cellular action with the
free representation on the `G`-orbits of `n`-cells. -/
def cellActionChainRepIsoFreeOrbitQuotient (n : ℕ) :
    letI := cellMulAction hcell n
    Rep.of (cellActionChainRepresentation C hcell R n) ≅
      Rep.free R G (MulAction.orbitRel.Quotient G (cell C n)) :=
  letI := cellMulAction hcell n
  cellActionChainRepIsoFree C hcell hfree R Quotient.out
    (by
      have h : (fun o : MulAction.orbitRel.Quotient G (cell C n) ↦ Quotient.mk'' o.out) = id :=
        funext Quotient.out_eq'
      exact h ▸ Function.bijective_id)

/-- Under `TauCeti.cellActionChainRepIsoFreeOrbitQuotient`, the generator `single o (single g 1)`
maps to the `g`-translate in cellular chains of the orbit representative `o.out`. -/
@[simp]
theorem cellActionChainRepIsoFreeOrbitQuotient_inv_hom_single {n : ℕ}
    (o : letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) (g : G) :
    letI := cellMulAction hcell n
    (cellActionChainRepIsoFreeOrbitQuotient C hcell hfree R n).inv.hom
        (Finsupp.single o (MonoidAlgebra.single g 1)) =
      cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n o.out) := by
  let := cellMulAction hcell n
  unfold cellActionChainRepIsoFreeOrbitQuotient
  exact cellActionChainRepIsoFree_inv_hom_single _ _ _ _ _ _ o g

/-- Under `TauCeti.cellActionChainRepIsoFreeOrbitQuotient`, the cellular basis vector of the orbit
representative `o.out` maps to the generator `single o (single 1 1)`. This is not a `simp` lemma
because `simp` unfolds `TauCeti.cellularChainBasis` first. -/
theorem cellActionChainRepIsoFreeOrbitQuotient_hom_hom_cellularChainBasis {n : ℕ}
    (o : letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) :
    letI := cellMulAction hcell n
    (cellActionChainRepIsoFreeOrbitQuotient C hcell hfree R n).hom.hom
        (cellularChainBasis C R n o.out) =
      Finsupp.single o (MonoidAlgebra.single 1 1) := by
  let := cellMulAction hcell n
  unfold cellActionChainRepIsoFreeOrbitQuotient
  exact cellActionChainRepIsoFree_hom_hom_cellularChainBasis _ _ _ _ _ _ o

/-- Under `TauCeti.cellActionChainRepIsoFreeOrbitQuotient`, the cellular basis vector of the
translate `g • o.out` maps to `single o (single g u⁻¹)` for the unit
`u = TauCeti.cellActionUnit C hcell R g o.out`. -/
theorem cellActionChainRepIsoFreeOrbitQuotient_hom_hom_cellularChainBasis_smul {n : ℕ}
    (o : letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) (g : G) :
    letI := cellMulAction hcell n
    (cellActionChainRepIsoFreeOrbitQuotient C hcell hfree R n).hom.hom
        (cellularChainBasis C R n (g • o.out)) =
      Finsupp.single o (MonoidAlgebra.single g (↑(cellActionUnit C hcell R g o.out)⁻¹ : R)) := by
  let := cellMulAction hcell n
  unfold cellActionChainRepIsoFreeOrbitQuotient
  exact cellActionChainRepIsoFree_hom_hom_cellularChainBasis_smul _ _ _ _ _ _ o g

include hfree in
/-- **Each term of the cellular chain complex of a free cellular action is projective in
`Rep R G`.** -/
theorem projective_cellActionChainComplexRep_X (n : ℕ) :
    Projective ((cellActionChainComplexRep C hcell R).X n) := by
  let := cellMulAction hcell n
  rw [cellActionChainComplexRep_X]
  exact Projective.of_iso (cellActionChainRepIsoFreeOrbitQuotient C hcell hfree R n).symm
    inferInstance

end Free

section OrbitSpace

variable {E B : Type w} [TopologicalSpace E] [TopologicalSpace B] [T2Space E]
  [CWComplex (univ : Set E)] {G : Type w} [Group G] [MulAction G E] {p : E → B}
  (hp : IsQuotientCoveringMap p G)
  (hcell : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    ∃ j : cell (univ : Set E) n, g • openCell n i = openCell n j)
  (hfree : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    g • openCell n i = openCell n i → g = 1)
  (R : Type w) [CommRing R] {n : ℕ}
  (s : (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) → cell (univ : Set E) n)
  (hs : letI := hp.cwComplexQuotient hcell hfree
    ∀ b, p '' openCell n (s b) = openCell n b)

include hs in
/-- A choice of lift `s b` of each `n`-cell `b` of the orbit space `B` gives a bijection onto the
`G`-orbits of `n`-cells of `E`. -/
private theorem bijective_quotient_mk_of_image_openCell :
    letI := hp.cwComplexQuotient hcell hfree
    letI := cellMulAction hcell n
    Function.Bijective (fun b ↦ (Quotient.mk'' (s b) :
      MulAction.orbitRel.Quotient G (cell (univ : Set E) n))) := by
  let := hp.cwComplexQuotient hcell hfree
  let := cellMulAction hcell n
  have heq : (fun b ↦ (Quotient.mk'' (s b) :
      MulAction.orbitRel.Quotient G (cell (univ : Set E) n))) =
      hp.cellQuotientEquiv hcell hfree n :=
    funext fun b ↦ (hp.quotient_mk_eq_cellQuotientEquiv_iff hcell hfree).2 (hs b)
  exact heq ▸ (hp.cellQuotientEquiv hcell hfree n).bijective

/-- **The cellular chains of the total space of a free cellular quotient covering are free over
`R[G]`, with basis one chosen lift of each cell of the orbit space `B`.** -/
def quotientCellularChainRepIsoFree :
    letI := hp.cwComplexQuotient hcell hfree
    haveI := hp.toContinuousConstSMul
    Rep.of (cellActionChainRepresentation (univ : Set E) hcell R n) ≅
      Rep.free R G (cell (univ : Set B) n) :=
  letI := hp.cwComplexQuotient hcell hfree
  haveI := hp.toContinuousConstSMul
  cellActionChainRepIsoFree (univ : Set E) hcell hfree R s
    (bijective_quotient_mk_of_image_openCell hp hcell hfree s hs)

/-- Under `TauCeti.quotientCellularChainRepIsoFree`, the generator `single b (single g 1)` maps to
the `g`-translate in cellular chains of the lifted cell `s b`. -/
@[simp]
theorem quotientCellularChainRepIsoFree_inv_hom_single
    (b : letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) (g : G) :
    letI := hp.cwComplexQuotient hcell hfree
    haveI := hp.toContinuousConstSMul
    (quotientCellularChainRepIsoFree hp hcell hfree R s hs).inv.hom
        (Finsupp.single b (MonoidAlgebra.single g 1)) =
      cellActionChainRepresentation (univ : Set E) hcell R n g
        (cellularChainBasis (univ : Set E) R n (s b)) := by
  let := hp.cwComplexQuotient hcell hfree
  have := hp.toContinuousConstSMul
  unfold quotientCellularChainRepIsoFree
  exact cellActionChainRepIsoFree_inv_hom_single _ _ _ _ _ _ b g

/-- Under `TauCeti.quotientCellularChainRepIsoFree`, the cellular basis vector of the chosen lift
`s b` maps to the generator `single b (single 1 1)`. This is not a `simp` lemma because `simp`
unfolds `TauCeti.cellularChainBasis` first. -/
theorem quotientCellularChainRepIsoFree_hom_hom_cellularChainBasis
    (b : letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) :
    letI := hp.cwComplexQuotient hcell hfree
    haveI := hp.toContinuousConstSMul
    (quotientCellularChainRepIsoFree hp hcell hfree R s hs).hom.hom
        (cellularChainBasis (univ : Set E) R n (s b)) =
      Finsupp.single b (MonoidAlgebra.single 1 1) := by
  let := hp.cwComplexQuotient hcell hfree
  have := hp.toContinuousConstSMul
  unfold quotientCellularChainRepIsoFree
  exact cellActionChainRepIsoFree_hom_hom_cellularChainBasis _ _ _ _ _ _ b

/-- Under `TauCeti.quotientCellularChainRepIsoFree`, the cellular basis vector of the translated
lift `g • s b` maps to `single b (single g u⁻¹)` for the unit
`u = TauCeti.cellActionUnit (univ : Set E) hcell R g (s b)`. -/
theorem quotientCellularChainRepIsoFree_hom_hom_cellularChainBasis_smul
    (b : letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) (g : G) :
    letI := hp.cwComplexQuotient hcell hfree
    letI := cellMulAction hcell n
    haveI := hp.toContinuousConstSMul
    (quotientCellularChainRepIsoFree hp hcell hfree R s hs).hom.hom
        (cellularChainBasis (univ : Set E) R n (g • s b)) =
      Finsupp.single b (MonoidAlgebra.single g
        (↑(cellActionUnit (univ : Set E) hcell R g (s b))⁻¹ : R)) := by
  let := hp.cwComplexQuotient hcell hfree
  let := cellMulAction hcell n
  have := hp.toContinuousConstSMul
  unfold quotientCellularChainRepIsoFree
  exact cellActionChainRepIsoFree_hom_hom_cellularChainBasis_smul _ _ _ _ _ _ b g

end OrbitSpace

section Augmentation

variable {E : Type w} [TopologicalSpace E] [T2Space E] (C : Set E) [CWComplex C]
  {G : Type w} [Monoid G] [MulAction G E] [ContinuousConstSMul G E]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n), ∃ j : cell C n, g • openCell n i = openCell n j)
  (R : Type w) [Ring R]

/-- The **augmentation** of the cellular chains of `C` in degree `0`, as a morphism to the trivial
representation: continuous translations carrying open cells onto open cells are cellular, and the
cellular augmentation is natural under cellular maps. -/
def cellActionAugmentationRep :
    Rep.of (cellActionChainRepresentation C hcell R 0) ⟶ Rep.trivial R G R :=
  cellularActionAugmentation C (fun g ↦ cellActionSMul C g (hcell g))
    (fun g ↦ isCellular_cellActionSMul C g (hcell g)) (cellActionSMul_one C (hcell 1))
    (fun g h ↦ cellActionSMul_mul C (hcell g) (hcell h) (hcell (g * h))) R

/-- The underlying linear map of `TauCeti.cellActionAugmentationRep` is the cellular augmentation
of `C`. -/
@[simp]
theorem cellActionAugmentationRep_hom_toLinearMap :
    (cellActionAugmentationRep C hcell R).hom.toLinearMap =
      (cellularAugmentation C (ModuleCat.of R R)).hom := by
  unfold cellActionAugmentationRep
  exact cellularActionAugmentation_hom_toLinearMap _ _ _ _ _ _

/-- The equivariant cellular augmentation vanishes on the boundaries of `1`-cells. -/
@[reassoc (attr := simp)]
theorem cellActionDifferentialRep_comp_cellActionAugmentationRep :
    cellActionDifferentialRep C hcell R 0 ≫ cellActionAugmentationRep C hcell R = 0 := by
  unfold cellActionDifferentialRep cellActionAugmentationRep
  exact cellularActionDifferential_comp_cellularActionAugmentation _ _ _ _ _ _

/-- The **augmentation of `TauCeti.cellActionChainComplexRep`**, as a chain map in
`ChainComplex (Rep R G) ℕ` to the trivial representation placed in degree `0`. -/
def cellActionChainComplexRepAugmentation :
    cellActionChainComplexRep C hcell R ⟶
      (ChainComplex.single₀ (Rep.{w} R G)).obj (Rep.trivial R G R) :=
  cellularActionComplexAugmentation C (fun g ↦ cellActionSMul C g (hcell g))
    (fun g ↦ isCellular_cellActionSMul C g (hcell g)) (cellActionSMul_one C (hcell 1))
    (fun g h ↦ cellActionSMul_mul C (hcell g) (hcell h) (hcell (g * h))) R

/-- In degree `0` the chain-map augmentation is `TauCeti.cellActionAugmentationRep`. -/
@[simp]
theorem cellActionChainComplexRepAugmentation_f_zero :
    (cellActionChainComplexRepAugmentation C hcell R).f 0 =
      eqToHom (cellActionChainComplexRep_X C hcell R 0) ≫ cellActionAugmentationRep C hcell R := by
  unfold cellActionChainComplexRepAugmentation cellActionAugmentationRep
  exact cellularActionComplexAugmentation_f_zero _ _ _ _ _ _

/-- **When `C` is contractible, the equivariant cellular augmentation is a quasi-isomorphism.** -/
theorem quasiIso_cellActionChainComplexRepAugmentation [ContractibleSpace C] :
    QuasiIso (cellActionChainComplexRepAugmentation C hcell R) := by
  unfold cellActionChainComplexRepAugmentation
  exact quasiIso_cellularActionComplexAugmentation _ _ _ _ _ _

end Augmentation

section Resolution

variable {E : Type w} [TopologicalSpace E] [T2Space E] (C : Set E) [CWComplex C]
  {G : Type w} [Group G] [MulAction G E] [ContinuousConstSMul G E]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n), ∃ j : cell C n, g • openCell n i = openCell n j)
  (hfree : ∀ (g : G) (n : ℕ) (i : cell C n), g • openCell n i = openCell n i → g = 1)
  (R : Type w) [CommRing R]

/-- **The cellular chains of a contractible free `G`-CW complex form a projective resolution** of
the trivial representation `Rep.trivial R G R`. -/
def cellActionResolution [ContractibleSpace C] :
    ProjectiveResolution (Rep.trivial R G R) where
  complex := cellActionChainComplexRep C hcell R
  projective := projective_cellActionChainComplexRep_X C hcell hfree R
  π := cellActionChainComplexRepAugmentation C hcell R
  quasiIso := quasiIso_cellActionChainComplexRepAugmentation C hcell R

/-- The complex of `TauCeti.cellActionResolution` is `TauCeti.cellActionChainComplexRep`. -/
@[simp]
theorem cellActionResolution_complex [ContractibleSpace C] :
    (cellActionResolution C hcell hfree R).complex = cellActionChainComplexRep C hcell R :=
  (rfl)

-- A public statement cannot unfold the unexposed body of `TauCeti.cellActionResolution`, so the
-- source of its `π` is transported along `cellActionResolution_complex`; inside this module that
-- transport is definitionally `𝟙 _`.
/-- The augmentation of `TauCeti.cellActionResolution` is
`TauCeti.cellActionChainComplexRepAugmentation`. -/
@[simp]
theorem cellActionResolution_π [ContractibleSpace C] :
    (cellActionResolution C hcell hfree R).π =
      eqToHom (cellActionResolution_complex C hcell hfree R) ≫
        cellActionChainComplexRepAugmentation C hcell R :=
  (Category.id_comp _).symm

end Resolution

end TauCeti
