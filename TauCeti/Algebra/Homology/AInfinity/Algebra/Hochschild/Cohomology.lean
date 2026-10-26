/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hochschild.Complex
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The Gerstenhaber bracket on positive-arity Hochschild cohomology

The Gerstenhaber bracket of closed suspended cochains is closed, and bracketing a boundary
with a closed cochain gives a boundary. Thus the bracket descends to the cohomology of the
positive-arity suspended Hochschild complex. We use Mathlib's explicit kernel/image homology
for short complexes of modules, with its canonical comparison to categorical homology.
The resulting bracket is bilinear, graded antisymmetric, and satisfies the graded Jacobi
identity. Its degrees are suspended degrees, in which the bracket has degree zero.

Arity-zero cochains and the cup product are not included here. In particular the cohomology
in this file is that of the positive-arity subcomplex, not unrestricted Hochschild cohomology.

## References

* M. Gerstenhaber, *The cohomology structure of an associative ring*.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti.AInfinityAlgebra.PositiveHochschild

open ReducedTensorWords

universe uR uA

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  (𝒜 : AInfinityAlgebra R A)

/-- The adjacent differentials computing positive-arity Hochschild cohomology in degree `p`.
The abbreviation keeps the three homogeneous cochain modules as its carriers. -/
private abbrev shortComplex (p : ℤ) : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk (d 𝒜 (p - 1) p (by omega)) (d 𝒜 p (p + 1) rfl)
    (LinearMap.ext (d_d 𝒜 (p - 1) p (p + 1) (by omega) rfl))

/-- Closed positive-arity suspended Hochschild cochains. -/
def cycles (p : ℤ) : Submodule R (cochains 𝒜 p) :=
  (d 𝒜 p (p + 1) rfl).ker

/-- A homogeneous cochain is closed exactly when its Hochschild differential vanishes. -/
@[simp]
theorem mem_cycles {p : ℤ} {F : cochains 𝒜 p} :
    F ∈ cycles 𝒜 p ↔ 𝒜.hochschildDifferential p F = 0 := by
  rw [cycles, LinearMap.mem_ker, ← Subtype.coe_inj, coe_d, ZeroMemClass.coe_zero]

/-- The inherited additive group of closed cochains, cached locally so quotient instance
synthesis does not have to reconstruct the additive group of the nested submodule. -/
local instance cyclesAddCommGroup (p : ℤ) : AddCommGroup (cycles 𝒜 p) :=
  (cycles 𝒜 p).addCommGroup

/-- The differential with codomain restricted to the closed cochains. -/
abbrev toCycles (p : ℤ) : cochains 𝒜 (p - 1) →ₗ[R] cycles 𝒜 p :=
  (d 𝒜 (p - 1) p (by omega)).codRestrict _ fun F ↦ by
    rw [cycles, LinearMap.mem_ker]
    exact d_d 𝒜 (p - 1) p (p + 1) (by omega) rfl F

@[simp]
theorem coe_toCycles (p : ℤ) (F : cochains 𝒜 (p - 1)) :
    (toCycles 𝒜 p F : cochains 𝒜 p) = d 𝒜 (p - 1) p (by omega) F := (rfl)

/-- Positive-arity suspended Hochschild cohomology: closed cochains modulo boundaries. -/
abbrev Cohomology (p : ℤ) := cycles 𝒜 p ⧸ (toCycles 𝒜 p).range

/-- The explicit quotient is canonically isomorphic to the categorical cohomology of the
positive-arity suspended Hochschild complex. -/
def cohomologyIso (p : ℤ) :
    (complex 𝒜).homology p ≅ ModuleCat.of R (Cohomology 𝒜 p) :=
  (complex 𝒜).homologyIsoSc' (p - 1) p (p + 1) (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso
      (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by
          simp only [Iso.refl_hom]
          exact (complex_d 𝒜 (p - 1) p (by omega)).symm)
        (by
          simp only [Iso.refl_hom]
          exact (complex_d 𝒜 p (p + 1) rfl).symm) :
        (complex 𝒜).sc' (p - 1) p (p + 1) ≅ shortComplex 𝒜 p) ≪≫
      (shortComplex 𝒜 p).moduleCatHomologyIso

/-- The inverse comparison sends the quotient class of a closed cochain to its categorical
cohomology class. -/
@[simp]
theorem cohomologyIso_inv_mk (p : ℤ) (F : cycles 𝒜 p) :
    (cohomologyIso 𝒜 p).inv (Submodule.Quotient.mk F) =
      (complex 𝒜).homologyπ p ((complex 𝒜).cyclesMk F.val (p + 1) (by simp)
        (by
          -- The forgetful functor evaluates the same underlying module differential.
          change (complex 𝒜).d p (p + 1) F.val = 0
          rw [complex_d]
          exact F.2)) := by
  let e : (complex 𝒜).sc' (p - 1) p (p + 1) ≅ shortComplex 𝒜 p :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        simp only [Iso.refl_hom]
        exact (complex_d 𝒜 (p - 1) p (by omega)).symm)
      (by
        simp only [Iso.refl_hom]
        exact (complex_d 𝒜 p (p + 1) rfl).symm)
  let F' : (shortComplex 𝒜 p).moduleCatLeftHomologyData.K := ⟨F.val, F.2⟩
  -- Express the representative using the explicit homology data so naturality applies
  -- without unfolding the chosen categorical kernels or quotient maps.
  change ((shortComplex 𝒜 p).moduleCatLeftHomologyData.π ≫
    (shortComplex 𝒜 p).moduleCatHomologyIso.inv ≫ ShortComplex.homologyMap e.inv ≫
      ((complex 𝒜).homologyIsoSc' (p - 1) p (p + 1) (by simp) (by simp)).inv) F' = _
  rw [← ShortComplex.moduleCatCyclesIso_inv_π_assoc,
    ShortComplex.homologyπ_naturality_assoc, HomologicalComplex.π_homologyIsoSc'_inv]
  simp only [ModuleCat.comp_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective ((complex 𝒜).iCycles p)).mp inferInstance
  -- Compose before evaluating: the kernel comparison lemmas are morphism equalities.
  change ((shortComplex 𝒜 p).moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap e.inv ≫
    ((complex 𝒜).cyclesIsoSc' (p - 1) p (p + 1) (by simp) (by simp)).inv ≫
      (complex 𝒜).iCycles p) F' = _
  rw [HomologicalComplex.cyclesIsoSc'_inv_iCycles, ShortComplex.cyclesMap_i,
    ShortComplex.moduleCatCyclesIso_inv_iCycles_assoc]
  exact (HomologicalComplex.i_cyclesMk (complex 𝒜) F.val (p + 1) (by simp) _).symm

/-- A closed cochain is a boundary exactly when it is the differential of a cochain in the
previous degree. -/
theorem mem_range_toCycles {p : ℤ} {F : cycles 𝒜 p} :
    F ∈ (toCycles 𝒜 p).range ↔
      ∃ G : cochains 𝒜 (p - 1), 𝒜.hochschildDifferential (p - 1) G = F.val.val := by
  simp only [LinearMap.mem_range, Subtype.ext_iff, coe_toCycles, coe_d]

/-- The Gerstenhaber bracket of closed cochains is closed. -/
theorem bracket_mem_cycles {p q n : ℤ} (h : p + q = n)
    {F : cochains 𝒜 p} {G : cochains 𝒜 q}
    (hF : F ∈ cycles 𝒜 p) (hG : G ∈ cycles 𝒜 q) :
    bracket 𝒜 h F G ∈ cycles 𝒜 n := by
  rw [mem_cycles, coe_bracket, ← h]
  rw [𝒜.hochschildDifferential_gerstenhaberBracket
    ((mem_cochains 𝒜).mp F.2) ((mem_cochains 𝒜).mp G.2),
    (mem_cycles 𝒜).mp hF, (mem_cycles 𝒜).mp hG]
  simp

/-- The bracket restricted to closed cochains. -/
def cyclesBracket {p q n : ℤ} (h : p + q = n) :
    cycles 𝒜 p →ₗ[R] cycles 𝒜 q →ₗ[R] cycles 𝒜 n :=
  LinearMap.mk₂ R
    (fun F G ↦ ⟨bracket 𝒜 h F.val G.val, bracket_mem_cycles 𝒜 h F.2 G.2⟩)
    (fun _ _ _ ↦ Subtype.ext ((bracket 𝒜 h).map_add₂ _ _ _))
    (fun _ _ _ ↦ Subtype.ext ((bracket 𝒜 h).map_smul₂ _ _ _))
    (fun _ _ _ ↦ Subtype.ext (map_add (bracket 𝒜 h _) _ _))
    (fun _ _ _ ↦ Subtype.ext (map_smul (bracket 𝒜 h _) _ _))

@[simp]
theorem coe_cyclesBracket {p q n : ℤ} (h : p + q = n)
    (F : cycles 𝒜 p) (G : cycles 𝒜 q) :
    (cyclesBracket 𝒜 h F G : cochains 𝒜 n) = bracket 𝒜 h F.val G.val := by
  simp [cyclesBracket]

/-- Bracketing a boundary with a closed cochain gives a boundary. -/
theorem cyclesBracket_mem_range_left {p q n : ℤ} (h : p + q = n)
    {F : cycles 𝒜 p} (hF : F ∈ (toCycles 𝒜 p).range) (G : cycles 𝒜 q) :
    cyclesBracket 𝒜 h F G ∈ (toCycles 𝒜 n).range := by
  obtain ⟨U, hU⟩ := (mem_range_toCycles 𝒜).mp hF
  rw [mem_range_toCycles]
  refine ⟨bracket 𝒜 (show p - 1 + q = n - 1 by omega) U G.val, ?_⟩
  simp only [coe_bracket, coe_cyclesBracket]
  have hder := 𝒜.hochschildDifferential_gerstenhaberBracket
    ((mem_cochains 𝒜).mp U.2) ((mem_cochains 𝒜).mp G.val.2)
  rw [(mem_cycles 𝒜).mp G.2, gerstenhaberBracket_zero_right, smul_zero, add_zero,
    hU, show 1 + (p - 1) = p by omega] at hder
  simpa only [show p - 1 + q = n - 1 by omega] using hder

/-- Bracketing a closed cochain with a boundary gives a boundary. -/
theorem cyclesBracket_mem_range_right {p q n : ℤ} (h : p + q = n)
    (F : cycles 𝒜 p) {G : cycles 𝒜 q} (hG : G ∈ (toCycles 𝒜 q).range) :
    cyclesBracket 𝒜 h F G ∈ (toCycles 𝒜 n).range := by
  have hswap : cyclesBracket 𝒜 h F G =
      -negOnePowCast R (q * p) • cyclesBracket 𝒜 (show q + p = n by omega) G F := by
    apply Subtype.ext
    simp only [coe_cyclesBracket, Submodule.coe_smul]
    exact bracket_swap 𝒜 (show q + p = n by omega) h G.val F.val
  rw [hswap]
  exact Submodule.smul_mem _ _ (cyclesBracket_mem_range_left 𝒜 _ hG F)

/-- The Gerstenhaber bracket on positive-arity suspended Hochschild cohomology. -/
def cohomologyBracket {p q n : ℤ} (h : p + q = n) :
    Cohomology 𝒜 p →ₗ[R] Cohomology 𝒜 q →ₗ[R] Cohomology 𝒜 n :=
  ((cyclesBracket 𝒜 h).compr₂ (toCycles 𝒜 n).range.mkQ).liftQ₂ _ _
    (fun _ hF ↦ LinearMap.ext fun G ↦ (Submodule.Quotient.mk_eq_zero _).mpr
      (cyclesBracket_mem_range_left 𝒜 h hF G))
    (fun _ hG ↦ LinearMap.ext fun F ↦ (Submodule.Quotient.mk_eq_zero _).mpr
      (cyclesBracket_mem_range_right 𝒜 h F hG))

/-- The bracket of cohomology classes is represented by the bracket of closed cochains. -/
@[simp]
theorem cohomologyBracket_mk {p q n : ℤ} (h : p + q = n)
    (F : cycles 𝒜 p) (G : cycles 𝒜 q) :
    cohomologyBracket 𝒜 h (Submodule.Quotient.mk F) (Submodule.Quotient.mk G) =
      Submodule.Quotient.mk (cyclesBracket 𝒜 h F G) := (rfl)

/-- Graded antisymmetry of the bracket on cohomology. -/
theorem cohomologyBracket_swap {p q n : ℤ} (h : p + q = n) (h' : q + p = n)
    (x : Cohomology 𝒜 p) (y : Cohomology 𝒜 q) :
    cohomologyBracket 𝒜 h' y x = -negOnePowCast R (p * q) • cohomologyBracket 𝒜 h x y := by
  induction x using Submodule.Quotient.induction_on with
  | H F =>
    induction y using Submodule.Quotient.induction_on with
    | H G =>
      have hs : cyclesBracket 𝒜 h' G F = -negOnePowCast R (p * q) • cyclesBracket 𝒜 h F G := by
        apply Subtype.ext
        simp only [coe_cyclesBracket, Submodule.coe_smul]
        exact bracket_swap 𝒜 h h' F.val G.val
      simp only [cohomologyBracket_mk, hs, Submodule.Quotient.mk_smul]

/-- The graded Jacobi identity on positive-arity suspended Hochschild cohomology,
in Leibniz form. -/
theorem leibniz_cohomologyBracket {p q r n : ℤ} (h : p + q + r = n)
    (x : Cohomology 𝒜 p) (y : Cohomology 𝒜 q) (z : Cohomology 𝒜 r) :
    cohomologyBracket 𝒜 (show p + (q + r) = n by omega) x
        (cohomologyBracket 𝒜 rfl y z) =
      cohomologyBracket 𝒜 h (cohomologyBracket 𝒜 rfl x y) z +
        negOnePowCast R (p * q) •
          cohomologyBracket 𝒜 (show q + (p + r) = n by omega) y
            (cohomologyBracket 𝒜 rfl x z) := by
  induction x using Submodule.Quotient.induction_on with
  | H F =>
    induction y using Submodule.Quotient.induction_on with
    | H G =>
      induction z using Submodule.Quotient.induction_on with
      | H H =>
        simp only [cohomologyBracket_mk]
        have hj : cyclesBracket 𝒜 (show p + (q + r) = n by omega) F
              (cyclesBracket 𝒜 rfl G H) =
            cyclesBracket 𝒜 h (cyclesBracket 𝒜 rfl F G) H +
              negOnePowCast R (p * q) • cyclesBracket 𝒜 (show q + (p + r) = n by omega) G
                (cyclesBracket 𝒜 rfl F H) := by
          apply Subtype.ext
          simp only [coe_cyclesBracket, Submodule.coe_add, Submodule.coe_smul]
          exact leibniz_bracket 𝒜 h F.val G.val H.val
        rw [hj, Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul]

end TauCeti.AInfinityAlgebra.PositiveHochschild
