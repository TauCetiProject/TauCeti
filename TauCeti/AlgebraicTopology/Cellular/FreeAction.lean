/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.RepresentationTheory.Rep.Iso
public import TauCeti.AlgebraicTopology.Cellular.Equivariant
public import TauCeti.RepresentationTheory.FreeOfBasis
public import TauCeti.Topology.CWComplex.Classical.OrbitSpace
import Mathlib.LinearAlgebra.Basis.SMul
import TauCeti.GroupTheory.GroupAction.Free

/-!
# Cellular chains of free cellular actions

Let a group `G` act continuously on a Hausdorff CW complex `C ⊆ E` so that every element carries
each open `n`-cell onto an open `n`-cell (`TauCeti.cellMulAction`). In
`TauCeti.AlgebraicTopology.Cellular.Equivariant`, this produces the equivariant cellular chain
complex `TauCeti.cellActionChainComplexRep` in `Rep R G` together with the orientation units
`TauCeti.cellActionBasisUnit` by which `g` scales the cellular basis vector of `i` into that of
`g • i` (without requiring translations to preserve chosen characteristic maps strictly, unlike the
lifted CW structure `TauCeti.cwComplexPreimage`).

Given any equivariant parametrization `(Σ _ : ι, G) ≃ cell C n`, rescaling the cellular basis along
each fibre by the units from its identity representative produces a `G`-permuted basis, identifying
the `n`-th cellular chain group with `Rep.free R G ι` over a commutative ring `R`
(`TauCeti.cellActionChainRepIsoFreeOfEquiv`). When `G` acts freely on the cells, each cellular chain
group is therefore free over `R[G]` with one generator for each `G`-orbit of cells
(`TauCeti.cellActionChainRepIsoFreeOfOrbits`), and — when `p : E → B` is a quotient covering map
giving `B` the orbit CW structure `IsQuotientCoveringMap.cwComplexQuotient` — with basis one chosen
lift of each cell of `B` (`IsQuotientCoveringMap.cellActionChainRepIsoFree`).

When `C` is contractible, the equivariant cellular augmentation
(`TauCeti.cellActionChainComplexRepAugmentation`) is a quasi-isomorphism, packaging the cellular
chain complex of `C` as a projective resolution of the trivial representation `Rep.trivial R G R`
(`TauCeti.cellActionResolution`).

## Main definitions and results

* `TauCeti.cellActionChainRepIsoFreeOfEquiv`, `TauCeti.cellActionChainRepIsoFreeOfOrbits`, and
  `IsQuotientCoveringMap.cellActionChainRepIsoFree`: for an equivariant cell parametrization or a
  free cellular action, each cellular chain group is free over `R[G]` on the parameter set, on the
  cell orbits, or on chosen lifts of the cells of the orbit space `B`.
* `TauCeti.projective_cellActionChainComplexRep_X` and `TauCeti.cellActionResolution`: for a
  contractible CW complex with a free cellular group action, its cellular chains form a
  `ProjectiveResolution (Rep.trivial R G R)`.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section I.4 and Section II.4.
* T. tom Dieck, *Transformation Groups*, de Gruyter, 1987, Section II.1.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2.
-/

public section

noncomputable section

open CategoryTheory Function Set Topology Topology.RelCWComplex
open scoped Pointwise

universe w

namespace TauCeti

section GroupAction

variable {E : Type w} [TopologicalSpace E] [T2Space E] (C : Set E) [CWComplex C]
  {G : Type w} [Group G] [MulAction G E] [ContinuousConstSMul G E]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n), ∃ j : cell C n, g • openCell n i = openCell n j)

section EquivariantBasis

variable (R : Type w) [CommRing R]

/-- Given representatives `s : ι → cell C n` and an equivariant parametrization
`e : (Σ _ : ι, G) ≃ cell C n` of the `n`-cells of `C`, rescaling each cellular basis vector `j` by
the unit of `(e.symm j).2` at `s (e.symm j).1` yields an `R`-basis whose vectors are strictly
permuted by `G`. -/
private def rescaledCellularChainBasis {n : ℕ} {ι : Type w}
    (s : ι → cell C n) (e : (Σ _ : ι, G) ≃ cell C n) :
    Module.Basis (cell C n) R (cellularChainGroup C (ModuleCat.of R R) n : ModuleCat R) :=
  (cellularChainBasis C R n).unitsSMul fun j ↦
    cellActionBasisUnit C hcell R (e.symm j).2 (s (e.symm j).1)

/-- At `e ⟨o, g⟩`, the rescaled cellular basis vector is the `g`-translate in the cellular chain
representation of the cellular basis vector of the chosen representative `s o`. -/
private theorem rescaledCellularChainBasis_apply_equiv {n : ℕ} {ι : Type w}
    (s : ι → cell C n) (e : (Σ _ : ι, G) ≃ cell C n)
    (he : letI := cellMulAction hcell n; ∀ (g : G) (o : ι), e ⟨o, g⟩ = g • s o)
    (o : ι) (g : G) :
    rescaledCellularChainBasis C hcell R s e (e ⟨o, g⟩) =
      cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n (s o)) := by
  let := cellMulAction hcell n
  rw [rescaledCellularChainBasis, Module.Basis.unitsSMul_apply, Equiv.symm_apply_apply,
    Units.smul_def, val_cellActionBasisUnit, he g o,
    ← cellActionChainRepresentation_cellularChainBasis]

/-- `G` permutes `rescaledCellularChainBasis` strictly along left multiplication in the second
component of `e`. -/
private theorem cellActionChainRepresentation_rescaledCellularChainBasis {n : ℕ} {ι : Type w}
    (s : ι → cell C n) (e : (Σ _ : ι, G) ≃ cell C n)
    (he : letI := cellMulAction hcell n; ∀ (g : G) (o : ι), e ⟨o, g⟩ = g • s o)
    (g h : G) (o : ι) :
    cellActionChainRepresentation C hcell R n g
        (rescaledCellularChainBasis C hcell R s e (e ⟨o, h⟩)) =
      rescaledCellularChainBasis C hcell R s e (e ⟨o, g * h⟩) := by
  rw [rescaledCellularChainBasis_apply_equiv C hcell R s e he,
    rescaledCellularChainBasis_apply_equiv C hcell R s e he, map_mul, mul_apply_eq_comp]

/-- Equivalence with the free representation associated to an equivariant parametrization of the
`n`-cells. -/
private def freeEquivCellActionChainRepresentation {n : ℕ} {ι : Type w}
    (s : ι → cell C n) (e : (Σ _ : ι, G) ≃ cell C n)
    (he : letI := cellMulAction hcell n; ∀ (g : G) (o : ι), e ⟨o, g⟩ = g • s o) :
    (Representation.free R G ι).Equiv (cellActionChainRepresentation C hcell R n) :=
  (cellActionChainRepresentation C hcell R n).freeEquivOfBasis
    (rescaledCellularChainBasis C hcell R s e) e
    (cellActionChainRepresentation_rescaledCellularChainBasis C hcell R s e he)

/-- **An equivariant parametrization `(Σ _ : ι, G) ≃ cell C n` of the `n`-cells identifies the
`n`-th cellular chain group in `Rep R G` with the free representation on `ι`**, with
`single o (single 1 1)` corresponding to the cellular basis vector of `s o` and
`single o (single g r)` to `r` times its `g`-translate. -/
def cellActionChainRepIsoFreeOfEquiv {n : ℕ} {ι : Type w}
    (s : ι → cell C n) (e : (Σ _ : ι, G) ≃ cell C n)
    (he : letI := cellMulAction hcell n; ∀ (g : G) (o : ι), e ⟨o, g⟩ = g • s o) :
    Rep.of (cellActionChainRepresentation C hcell R n) ≅ Rep.free R G ι :=
  (Rep.mkIso (freeEquivCellActionChainRepresentation C hcell R s e he)).symm

/-- Under `TauCeti.cellActionChainRepIsoFreeOfEquiv`, the generator `single o (single g r)` of the
free representation maps to `r` times the `g`-translate of the cellular basis vector of the chosen
representative `s o`. -/
@[simp]
theorem cellActionChainRepIsoFreeOfEquiv_inv_hom_single {n : ℕ} {ι : Type w}
    (s : ι → cell C n) (e : (Σ _ : ι, G) ≃ cell C n)
    (he : letI := cellMulAction hcell n; ∀ (g : G) (o : ι), e ⟨o, g⟩ = g • s o)
    (o : ι) (g : G) (r : R) :
    (cellActionChainRepIsoFreeOfEquiv C hcell R s e he).inv.hom
        (Finsupp.single o (MonoidAlgebra.single g r)) =
      r • cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n (s o)) := by
  rw [cellActionChainRepIsoFreeOfEquiv, Iso.symm_inv, Rep.mkIso_hom_hom_apply]
  exact (Representation.freeEquivOfBasis_single (cellActionChainRepresentation C hcell R n)
    (rescaledCellularChainBasis C hcell R s e) e _ o g r).trans
      (by rw [rescaledCellularChainBasis_apply_equiv C hcell R s e he])

/-- Under `TauCeti.cellActionChainRepIsoFreeOfEquiv`, the cellular basis vector of `s o` corresponds
to the generator `single o (single 1 1)`. This is not a `simp` lemma because `simp` unfolds
`TauCeti.cellularChainBasis` first. -/
theorem cellActionChainRepIsoFreeOfEquiv_hom_hom_cellularChainBasis {n : ℕ} {ι : Type w}
    (s : ι → cell C n) (e : (Σ _ : ι, G) ≃ cell C n)
    (he : letI := cellMulAction hcell n; ∀ (g : G) (o : ι), e ⟨o, g⟩ = g • s o)
    (o : ι) :
    (cellActionChainRepIsoFreeOfEquiv C hcell R s e he).hom.hom
        (cellularChainBasis C R n (s o)) =
      Finsupp.single o (MonoidAlgebra.single 1 1) := by
  have h := cellActionChainRepIsoFreeOfEquiv_inv_hom_single C hcell R s e he o 1 1
  rw [map_one, one_apply_eq_self, one_smul] at h
  rw [← h, Rep.hom_inv_apply]

/-- Under `TauCeti.cellActionChainRepIsoFreeOfEquiv`, the cellular basis vector of a translated
representative `g • s o` maps to `single o` weighted at `g` by the inverse orientation unit
`(cellActionBasisUnit C hcell R g (s o))⁻¹`. -/
theorem cellActionChainRepIsoFreeOfEquiv_hom_hom_cellularChainBasis_smul {n : ℕ} {ι : Type w}
    (s : ι → cell C n) (e : (Σ _ : ι, G) ≃ cell C n)
    (he : letI := cellMulAction hcell n; ∀ (g : G) (o : ι), e ⟨o, g⟩ = g • s o)
    (o : ι) (g : G) :
    letI := cellMulAction hcell n
    (cellActionChainRepIsoFreeOfEquiv C hcell R s e he).hom.hom
        (cellularChainBasis C R n (g • s o)) =
      Finsupp.single o
        (MonoidAlgebra.single g (↑(cellActionBasisUnit C hcell R g (s o))⁻¹ : R)) := by
  let := cellMulAction hcell n
  have h := cellActionChainRepIsoFreeOfEquiv_inv_hom_single C hcell R s e he o g
    (↑(cellActionBasisUnit C hcell R g (s o))⁻¹ : R)
  rw [cellActionChainRepresentation_cellularChainBasis_unit, ← Units.smul_def, smul_smul,
    inv_mul_cancel, one_smul] at h
  rw [← h, Rep.hom_inv_apply]

end EquivariantBasis

section Free

variable (hfree : ∀ (g : G) (n : ℕ) (i : cell C n), g • openCell n i = openCell n i → g = 1)
  (R : Type w) [CommRing R]

/-- The orbit parametrization `(Σ _ : orbitRel.Quotient G (cell C n), G) ≃ cell C n` attached to a
section `φ` of the orbit quotient. -/
private def orbitSigmaEquiv {n : ℕ}
    (φ : (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) → cell C n)
    (hφ : letI := cellMulAction hcell n; LeftInverse Quotient.mk'' φ) :
    (Σ _ : (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)), G) ≃
      cell C n :=
  letI := cellMulAction hcell n
  haveI := isCancelSMul_cell hcell hfree n
  (Equiv.sigmaEquivProd _ G).trans
    (MulAction.selfEquivOrbitsQuotientProd' hφ IsCancelSMul.stabilizer_eq_bot).symm

/-- **The cellular chains of a free cellular action are free over the group ring on the cell
orbits.** Given a choice `φ o` of representative in each `G`-orbit of `n`-cells of `C`, the `n`-th
cellular chain group of `C` is isomorphic in `Rep R G` to the free representation on the `G`-orbits
of `n`-cells, with `single o (single 1 1)` corresponding to the cellular basis vector of `φ o` and
`single o (single g r)` to `r` times its `g`-translate. -/
def cellActionChainRepIsoFreeOfOrbits {n : ℕ}
    (φ : (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) → cell C n)
    (hφ : letI := cellMulAction hcell n; LeftInverse Quotient.mk'' φ) :
    Rep.of (cellActionChainRepresentation C hcell R n) ≅
      Rep.free R G (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) :=
  cellActionChainRepIsoFreeOfEquiv C hcell R φ
    (orbitSigmaEquiv C hcell hfree φ hφ) fun g o ↦ by
      let := cellMulAction hcell n
      have := isCancelSMul_cell hcell hfree n
      simp [orbitSigmaEquiv]

/-- Under `TauCeti.cellActionChainRepIsoFreeOfOrbits`, the generator `single o (single g r)` of the
free representation maps to `r` times the `g`-translate of the cellular basis vector of the chosen
orbit representative `φ o`. -/
@[simp]
theorem cellActionChainRepIsoFreeOfOrbits_inv_hom_single {n : ℕ}
    (φ : (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) → cell C n)
    (hφ : letI := cellMulAction hcell n; LeftInverse Quotient.mk'' φ)
    (o : letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) (g : G) (r : R) :
    (cellActionChainRepIsoFreeOfOrbits C hcell hfree R φ hφ).inv.hom
        (Finsupp.single o (MonoidAlgebra.single g r)) =
      r • cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n (φ o)) :=
  cellActionChainRepIsoFreeOfEquiv_inv_hom_single C hcell R φ _ _ o g r

/-- Under `TauCeti.cellActionChainRepIsoFreeOfOrbits`, the cellular basis vector of the chosen
representative `φ o` corresponds to the generator `single o (single 1 1)`. This is not a `simp`
lemma because `simp` unfolds `TauCeti.cellularChainBasis` first. -/
theorem cellActionChainRepIsoFreeOfOrbits_hom_hom_cellularChainBasis {n : ℕ}
    (φ : (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) → cell C n)
    (hφ : letI := cellMulAction hcell n; LeftInverse Quotient.mk'' φ)
    (o : letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) :
    (cellActionChainRepIsoFreeOfOrbits C hcell hfree R φ hφ).hom.hom
        (cellularChainBasis C R n (φ o)) =
      Finsupp.single o (MonoidAlgebra.single 1 1) :=
  cellActionChainRepIsoFreeOfEquiv_hom_hom_cellularChainBasis C hcell R φ _ _ o

/-- Under `TauCeti.cellActionChainRepIsoFreeOfOrbits`, the cellular basis vector of a translated
orbit representative `g • φ o` maps to `single o` weighted at `g` by the inverse orientation unit
`(cellActionBasisUnit C hcell R g (φ o))⁻¹`. -/
theorem cellActionChainRepIsoFreeOfOrbits_hom_hom_cellularChainBasis_smul {n : ℕ}
    (φ : (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) → cell C n)
    (hφ : letI := cellMulAction hcell n; LeftInverse Quotient.mk'' φ)
    (o : letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) (g : G) :
    letI := cellMulAction hcell n
    (cellActionChainRepIsoFreeOfOrbits C hcell hfree R φ hφ).hom.hom
        (cellularChainBasis C R n (g • φ o)) =
      Finsupp.single o
        (MonoidAlgebra.single g (↑(cellActionBasisUnit C hcell R g (φ o))⁻¹ : R)) :=
  cellActionChainRepIsoFreeOfEquiv_hom_hom_cellularChainBasis_smul C hcell R φ _ _ o g

include hfree in
/-- Every term of `TauCeti.cellActionChainComplexRep` for a free cellular group action is a
projective object of `Rep R G`. -/
theorem projective_cellActionChainComplexRep_X (n : ℕ) :
    Projective ((cellActionChainComplexRep C hcell R).X n) := by
  rw [cellActionChainComplexRep_X]
  exact Projective.of_iso
    (cellActionChainRepIsoFreeOfOrbits C hcell hfree R Quotient.out
      (letI := cellMulAction hcell n; Quotient.out_eq')).symm
    inferInstance

include hfree in
/-- **The cellular chains of a contractible CW complex with a free cellular group action form a
projective resolution** of the trivial representation `Rep.trivial R G R`. -/
def cellActionResolution [ContractibleSpace C] :
    ProjectiveResolution (Rep.trivial R G R) where
  complex := cellActionChainComplexRep C hcell R
  projective := projective_cellActionChainComplexRep_X C hcell hfree R
  π := cellActionChainComplexRepAugmentation C hcell R
  quasiIso := quasiIso_cellActionChainComplexRepAugmentation C hcell R

/-- The underlying chain complex of `TauCeti.cellActionResolution` is
`TauCeti.cellActionChainComplexRep`. -/
@[simp]
theorem cellActionResolution_complex [ContractibleSpace C] :
    (cellActionResolution C hcell hfree R).complex = cellActionChainComplexRep C hcell R :=
  (rfl)

-- Under `module`, the public statement cannot unfold the unexposed body of
-- `TauCeti.cellActionResolution`, so it transports along `cellActionResolution_complex`.
/-- The augmentation of `TauCeti.cellActionResolution` is
`TauCeti.cellActionChainComplexRepAugmentation`. -/
@[simp]
theorem cellActionResolution_π [ContractibleSpace C] :
    (cellActionResolution C hcell hfree R).π =
      eqToHom (cellActionResolution_complex C hcell hfree R) ≫
        cellActionChainComplexRepAugmentation C hcell R :=
  (Category.id_comp _).symm

end Free

end GroupAction

section QuotientCovering

variable {E B : Type w} [TopologicalSpace E] [T2Space E] [CWComplex (univ : Set E)]
  [TopologicalSpace B] {G : Type w} [Group G] [MulAction G E] {p : E → B}
  (hp : IsQuotientCoveringMap p G)
  (hcell : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    ∃ j : cell (univ : Set E) n, g • openCell n i = openCell n j)
  (hfree : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    g • openCell n i = openCell n i → g = 1)
  (R : Type w) [CommRing R]

/-- **The cellular chains of the total space of a free cellular quotient covering are free over the
group ring, with basis one chosen lift of each cell of the orbit space.** Given a lift `s b` of each
`n`-cell `b` of `B` (for the orbit CW structure `IsQuotientCoveringMap.cwComplexQuotient`), the
`n`-th cellular chain group of `E` is isomorphic in `Rep R G` to
`Rep.free R G (cell (univ : Set B) n)`, with `single b (single 1 1)` corresponding to the cellular
basis vector of `s b` and `single b (single g r)` to `r` times its `g`-translate. -/
def _root_.IsQuotientCoveringMap.cellActionChainRepIsoFree {n : ℕ}
    (s : (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) → cell (univ : Set E) n)
    (hs : letI := hp.cwComplexQuotient hcell hfree; ∀ b, p '' openCell n (s b) = openCell n b) :
    haveI := hp.toContinuousConstSMul
    Rep.of (cellActionChainRepresentation (univ : Set E) hcell R n) ≅
      Rep.free R G (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) :=
  haveI := hp.toContinuousConstSMul
  cellActionChainRepIsoFreeOfEquiv (univ : Set E) hcell R s
    (hp.sigmaSMulQuotientLiftEquiv hcell hfree s hs)
    fun g b ↦ hp.sigmaSMulQuotientLiftEquiv_apply hcell hfree s hs ⟨b, g⟩

/-- Under `IsQuotientCoveringMap.cellActionChainRepIsoFree`, the generator `single b (single g r)`
of the free representation on the `n`-cells of `B` maps to `r` times the `g`-translate of the
cellular basis vector of the lifted cell `s b`. -/
@[simp]
theorem _root_.IsQuotientCoveringMap.cellActionChainRepIsoFree_inv_hom_single {n : ℕ}
    (s : (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) → cell (univ : Set E) n)
    (hs : letI := hp.cwComplexQuotient hcell hfree; ∀ b, p '' openCell n (s b) = openCell n b)
    (b : letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) (g : G) (r : R) :
    haveI := hp.toContinuousConstSMul
    (hp.cellActionChainRepIsoFree hcell hfree R s hs).inv.hom
        (Finsupp.single b (MonoidAlgebra.single g r)) =
      r • cellActionChainRepresentation (univ : Set E) hcell R n g
        (cellularChainBasis (univ : Set E) R n (s b)) :=
  haveI := hp.toContinuousConstSMul
  cellActionChainRepIsoFreeOfEquiv_inv_hom_single (univ : Set E) hcell R s _ _ b g r

/-- Under `IsQuotientCoveringMap.cellActionChainRepIsoFree`, the cellular basis vector of the chosen
lift `s b` corresponds to the generator `single b (single 1 1)`. This is not a `simp` lemma because
`simp` unfolds `TauCeti.cellularChainBasis` first. -/
theorem _root_.IsQuotientCoveringMap.cellActionChainRepIsoFree_hom_hom_cellularChainBasis {n : ℕ}
    (s : (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) → cell (univ : Set E) n)
    (hs : letI := hp.cwComplexQuotient hcell hfree; ∀ b, p '' openCell n (s b) = openCell n b)
    (b : letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) :
    haveI := hp.toContinuousConstSMul
    (hp.cellActionChainRepIsoFree hcell hfree R s hs).hom.hom
        (cellularChainBasis (univ : Set E) R n (s b)) =
      Finsupp.single b (MonoidAlgebra.single 1 1) :=
  haveI := hp.toContinuousConstSMul
  cellActionChainRepIsoFreeOfEquiv_hom_hom_cellularChainBasis (univ : Set E) hcell R s _ _ b

/-- Under `IsQuotientCoveringMap.cellActionChainRepIsoFree`, the cellular basis vector of the
translated lift `g • s b` maps to `single b` weighted at `g` by the inverse orientation unit
`(cellActionBasisUnit (univ : Set E) hcell R g (s b))⁻¹`. -/
theorem _root_.IsQuotientCoveringMap.cellActionChainRepIsoFree_hom_hom_cellularChainBasis_smul
    {n : ℕ}
    (s : (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) → cell (univ : Set E) n)
    (hs : letI := hp.cwComplexQuotient hcell hfree; ∀ b, p '' openCell n (s b) = openCell n b)
    (b : letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) (g : G) :
    letI := cellMulAction hcell n
    haveI := hp.toContinuousConstSMul
    (hp.cellActionChainRepIsoFree hcell hfree R s hs).hom.hom
        (cellularChainBasis (univ : Set E) R n (g • s b)) =
      Finsupp.single b (MonoidAlgebra.single g
        (↑(cellActionBasisUnit (univ : Set E) hcell R g (s b))⁻¹ : R)) :=
  haveI := hp.toContinuousConstSMul
  cellActionChainRepIsoFreeOfEquiv_hom_hom_cellularChainBasis_smul
    (univ : Set E) hcell R s _ _ b g

end QuotientCovering

end TauCeti
