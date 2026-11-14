/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Lie
public import TauCeti.Algebra.Lie.Derivation.Basic
public import TauCeti.RingTheory.Kaehler.DeRham.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Interior contraction, Lie derivatives, and Cartan's calculus on the algebraic de Rham complex

Let `R` and `S` be commutative rings with `[Algebra R S]`. On the algebraic de Rham complex
`(ExteriorAlgebra S Ω[S⁄R], TauCeti.KaehlerDeRham.extDeriv R S)` two families of operators arise
from derivations of `S`:

1. **Interior contraction (`Derivation.deRhamInterior`)** for an `R`-linear derivation
   `δ : Derivation R S S`, obtained by contracting `ExteriorAlgebra S Ω[S⁄R]` against the induced
   `S`-linear functional `δ.liftKaehlerDifferential : Module.Dual S Ω[S⁄R]`. It is an `S`-linear
   odd derivation of degree `-1` satisfying `i_δ ∘ i_δ = 0` and
   `i_{δ₁} ∘ i_{δ₂} = - i_{δ₂} ∘ i_{δ₁}`.

2. **Lie derivatives (`Derivation.kaehlerLieDeriv`, `Derivation.deRhamLieDeriv`)** for a
   `k`-derivation `δ : Derivation k S S` over *any* auxiliary base ring `k` with `[Algebra k S]`
   (without requiring `δ` to vanish on `R`, covering for instance lifted base/total derivations in
   a ring tower `k → R → S`).

   A `k`-linear map `L : Ω[S⁄R] →ₗ[k] Ω[S⁄R]` satisfying `L (D R S s) = D R S (δ s)` exists **if
   and only if** `∀ r : R, D R S (δ (algebraMap R S r)) = 0`
   (`Derivation.exists_kaehlerLieDeriv_iff`).
   This condition holds automatically both for relative derivations `δ : Derivation R S S` and for
   compatible derivation pairs in `Derivation.couple k R S` (`δ` preserving the image of `R`).
   Whenever it holds:
   * `δ.kaehlerLieDeriv hδ : Module.End k Ω[S⁄R]` sends `D R S s` to `D R S (δ s)` and obeys
     `L (s • ω) = δ s • ω + s • L ω`;
   * `δ.deRhamLieDeriv hδ : Module.End k (ExteriorAlgebra S Ω[S⁄R])` is the unique `k`-linear
     derivation of `ExteriorAlgebra S Ω[S⁄R]` extending `δ` on `S` and commuting with
     `TauCeti.KaehlerDeRham.extDeriv R S` (`Derivation.deRhamLieDeriv_unique`);
   * `δ.deRhamLieDeriv hδ` preserves each exterior power `⋀[S]^n Ω[S⁄R]` and integer degree
     `TauCeti.KaehlerDeRham.grading R S p`, and respects Lie brackets (`⁅δ₁, δ₂⁆`), so commuting
     derivations of `S` lift to commuting derivations of `ExteriorAlgebra S Ω[S⁄R]` that commute
     with `extDeriv R S`.

Bundling these lifts yields Lie algebra homomorphisms
`TauCeti.KaehlerDeRham.lieDerivHom` (`Derivation R S S →ₗ⁅R⁆ Der_R (⋀ Ω[S⁄R])`) and
`TauCeti.KaehlerDeRham.coupleLieDerivHom` (`Derivation.couple k R S →ₗ⁅k⁆ Der_k (⋀ Ω[S⁄R])`).
Finally, for `δ, δ₁, δ₂ : Derivation R S S`, we prove **Cartan's magic formula**
`L_δ = d ∘ i_δ + i_δ ∘ d` (`Derivation.deRhamLieDeriv_eq_extDeriv_deRhamInterior_add`) and the
**Cartan commutator identity** `[L_{δ₁}, i_{δ₂}] = i_{⁅δ₁, δ₂⁆}`
(`Derivation.deRhamLieDeriv_deRhamInterior_sub`).

## Main definitions

* `Derivation.deRhamInterior`: interior contraction on `ExteriorAlgebra S Ω[S⁄R]` along
  `δ : Derivation R S S`.
* `Derivation.kaehlerLieDeriv`: Lie derivative on `Ω[S⁄R]` along `δ : Derivation k S S` satisfying
  `∀ r : R, D R S (δ (algebraMap R S r)) = 0`.
* `Derivation.deRhamLieDeriv`: Lie derivative on `ExteriorAlgebra S Ω[S⁄R]` along such `δ`.
* `TauCeti.KaehlerDeRham.lieDerivHom`: Lie algebra homomorphism from `Derivation R S S` to
  `TauCeti.derivationLieAlgebra R (ExteriorAlgebra S Ω[S⁄R])`.
* `TauCeti.KaehlerDeRham.coupleLieDerivHom`: Lie algebra homomorphism from
  `Derivation.couple k R S` to `TauCeti.derivationLieAlgebra k (ExteriorAlgebra S Ω[S⁄R])`.

## Main results

* `Derivation.exists_kaehlerLieDeriv_iff`: necessary and sufficient condition for `δ` to induce an
  operator `D s ↦ D (δ s)` on `Ω[S⁄R]`.
* `Derivation.extDeriv_deRhamLieDeriv`: `extDeriv R S` commutes with `δ.deRhamLieDeriv hδ`.
* `Derivation.deRhamLieDeriv_unique`: `δ.deRhamLieDeriv hδ` is the unique algebra derivation of
  `ExteriorAlgebra S Ω[S⁄R]` extending `δ` on `S` and commuting with `extDeriv R S`.
* `Derivation.deRhamLieDeriv_commutator`: `(⁅δ₁, δ₂⁆).deRhamLieDeriv` is the commutator of
  `δ₁.deRhamLieDeriv` and `δ₂.deRhamLieDeriv`.
* `Derivation.deRhamLieDeriv_eq_extDeriv_deRhamInterior_add`: Cartan's magic formula
  `L_δ x = d (i_δ x) + i_δ (d x)`.
* `Derivation.deRhamLieDeriv_deRhamInterior_sub`: `[L_{δ₁}, i_{δ₂}] = i_{⁅δ₁, δ₂⁆}`.

## Implementation notes

`Derivation.kaehlerLieDeriv` and `Derivation.deRhamLieDeriv` assume only `[CommRing k]` and
`[Algebra k S]` (alongside `[CommRing R]` and `[Algebra R S]`), without requiring `[Algebra k R]`
or `[IsScalarTower k R S]`: `SMulCommClass R k S` holds automatically for commutative base rings,
so `Ω[S⁄R]` and `ExteriorAlgebra S Ω[S⁄R]` inherit `Module k` and `Algebra k` structures directly
from `[Algebra k S]`. Tower hypotheses `[Algebra k R] [IsScalarTower k R S]` are introduced only
when scalar-multiplying derivations (`Derivation.smul_deRhamLieDeriv`) or packaging
`Derivation.couple k R S` (`TauCeti.KaehlerDeRham.coupleLieDerivHom`).

To extend `δ.kaehlerLieDeriv hδ` from `Ω[S⁄R]` to an even algebra derivation of
`ExteriorAlgebra S Ω[S⁄R]` via `ExteriorAlgebra.lift`, we use a private square-zero ring
`EvenDual R S` with carrier `A × A` and derivation-twisted `S`-algebra map
`s ↦ (algebraMap S A s, algebraMap S A (δ s))`. Defining `EvenDual R S` as a private structure
rather than reusing `TrivSqZeroExt A A` avoids an `SMul S` diamond with `TrivSqZeroExt`'s global
untwisted `Algebra S` instance (`s ↦ (algebraMap S A s, 0)`).

## References

* N. Bourbaki, *Algebra*, Chapter III, §10.
* I. M. Anderson, *The Variational Bicomplex*, Chapter 1.
-/

public section

open CliffordAlgebra TauCeti.KaehlerDeRham

namespace Derivation

/-! ### Interior contraction along an `R`-derivation -/

section Interior

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **Interior contraction** (`i_δ`) of an `R`-derivation `δ : Derivation R S S` on the algebraic
de Rham algebra `ExteriorAlgebra S Ω[S⁄R]`, defined by left contraction against the universal lift
`δ.liftKaehlerDifferential : Module.Dual S Ω[S⁄R]`. -/
noncomputable def deRhamInterior (δ : Derivation R S S) :
    ExteriorAlgebra S Ω[S⁄R] →ₗ[S] ExteriorAlgebra S Ω[S⁄R] :=
  contractLeft (Q := (0 : QuadraticForm S Ω[S⁄R])) δ.liftKaehlerDifferential

/-- Unfolding lemma relating `δ.deRhamInterior` to `CliffordAlgebra.contractLeft`. -/
theorem deRhamInterior_def (δ : Derivation R S S) :
    δ.deRhamInterior =
      contractLeft (Q := (0 : QuadraticForm S Ω[S⁄R])) δ.liftKaehlerDifferential :=
  (rfl)

/-- Interior contraction annihilates degree-zero elements `algebraMap S _ s`. -/
@[simp]
theorem deRhamInterior_algebraMap (δ : Derivation R S S) (s : S) :
    δ.deRhamInterior (algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s) = 0 :=
  contractLeft_algebraMap (Q := (0 : QuadraticForm S Ω[S⁄R])) δ.liftKaehlerDifferential s

/-- Interior contraction annihilates `1`. -/
@[simp]
theorem deRhamInterior_one (δ : Derivation R S S) :
    δ.deRhamInterior 1 = 0 :=
  contractLeft_one (Q := (0 : QuadraticForm S Ω[S⁄R])) δ.liftKaehlerDifferential

/-- On a `1`-form `ι ω`, interior contraction evaluates `δ.liftKaehlerDifferential ω`. -/
@[simp]
theorem deRhamInterior_ι (δ : Derivation R S S) (ω : Ω[S⁄R]) :
    δ.deRhamInterior (ExteriorAlgebra.ι S ω) =
      algebraMap S (ExteriorAlgebra S Ω[S⁄R]) (δ.liftKaehlerDifferential ω) :=
  contractLeft_ι (0 : QuadraticForm S Ω[S⁄R]) δ.liftKaehlerDifferential ω

/-- Contracting an exact `1`-form `ι (D R S s)` yields `algebraMap S _ (δ s)`. -/
theorem deRhamInterior_ι_D (δ : Derivation R S S) (s : S) :
    δ.deRhamInterior (ExteriorAlgebra.ι S (KaehlerDifferential.D R S s)) =
      algebraMap S (ExteriorAlgebra S Ω[S⁄R]) (δ s) := by
  simp

/-- **Graded Leibniz rule** for interior contraction on `ExteriorAlgebra S Ω[S⁄R]`. -/
theorem deRhamInterior_mul (δ : Derivation R S S) (x y : ExteriorAlgebra S Ω[S⁄R]) :
    δ.deRhamInterior (x * y) =
      δ.deRhamInterior x * y +
        involute (Q := (0 : QuadraticForm S Ω[S⁄R])) x * δ.deRhamInterior y :=
  contractLeft_mul δ.liftKaehlerDifferential x y

/-- Interior contraction anticommutes with the grade involution. -/
theorem deRhamInterior_involute (δ : Derivation R S S) (x : ExteriorAlgebra S Ω[S⁄R]) :
    δ.deRhamInterior (involute (Q := (0 : QuadraticForm S Ω[S⁄R])) x) =
      -involute (Q := (0 : QuadraticForm S Ω[S⁄R])) (δ.deRhamInterior x) := by
  rw [deRhamInterior_def, involute_contractLeft, neg_neg]

/-- Repeated interior contraction along the same derivation vanishes (`i_δ ∘ i_δ = 0`). -/
@[simp]
theorem deRhamInterior_deRhamInterior (δ : Derivation R S S) (x : ExteriorAlgebra S Ω[S⁄R]) :
    δ.deRhamInterior (δ.deRhamInterior x) = 0 :=
  contractLeft_contractLeft (Q := (0 : QuadraticForm S Ω[S⁄R])) δ.liftKaehlerDifferential x

/-- Interior contractions along two `R`-derivations anticommute
(`i_{δ₁} ∘ i_{δ₂} = - i_{δ₂} ∘ i_{δ₁}`). -/
theorem deRhamInterior_comm (δ₁ δ₂ : Derivation R S S) (x : ExteriorAlgebra S Ω[S⁄R]) :
    δ₁.deRhamInterior (δ₂.deRhamInterior x) = -δ₂.deRhamInterior (δ₁.deRhamInterior x) :=
  contractLeft_comm (Q := (0 : QuadraticForm S Ω[S⁄R]))
    δ₁.liftKaehlerDifferential δ₂.liftKaehlerDifferential x

/-- Interior contraction maps `⋀[S]^(n + 1) Ω[S⁄R]` into `⋀[S]^n Ω[S⁄R]`. -/
theorem deRhamInterior_mem_exteriorPower (δ : Derivation R S S) {n : ℕ}
    {x : ExteriorAlgebra S Ω[S⁄R]} (hx : x ∈ ⋀[S]^(n + 1) Ω[S⁄R]) :
    δ.deRhamInterior x ∈ ⋀[S]^n Ω[S⁄R] :=
  TauCeti.ExteriorAlgebra.contractLeft_mem_exteriorPower δ.liftKaehlerDifferential hx

/-- Interior contraction lowers the integer degree in `grading R S` by one. -/
theorem deRhamInterior_mem_grading (δ : Derivation R S S) {p : ℤ}
    {x : ExteriorAlgebra S Ω[S⁄R]} (hx : x ∈ grading R S p) :
    δ.deRhamInterior x ∈ grading R S (p - 1) := by
  rw [mem_grading_iff, deRhamInterior_def]
  exact TauCeti.ExteriorAlgebra.contractLeft_mem_integerGrading δ.liftKaehlerDifferential
    (mem_grading_iff.mp hx)

/-- Interior contraction is additive in the derivation `δ`. -/
@[simp]
theorem deRhamInterior_add (δ₁ δ₂ : Derivation R S S) :
    (δ₁ + δ₂).deRhamInterior = δ₁.deRhamInterior + δ₂.deRhamInterior := by
  rw [deRhamInterior_def, deRhamInterior_def, deRhamInterior_def]
  have h : (δ₁ + δ₂).liftKaehlerDifferential =
      δ₁.liftKaehlerDifferential + δ₂.liftKaehlerDifferential :=
    (KaehlerDifferential.linearMapEquivDerivation R S).symm.map_add δ₁ δ₂
  rw [h, map_add]

/-- Interior contraction along the zero derivation vanishes. -/
@[simp]
theorem deRhamInterior_zero : (0 : Derivation R S S).deRhamInterior = 0 := by
  rw [deRhamInterior_def]
  have h : (0 : Derivation R S S).liftKaehlerDifferential = 0 :=
    (KaehlerDifferential.linearMapEquivDerivation R S).symm.map_zero
  rw [h, map_zero]

end Interior

/-! ### Lie derivative on Kähler differentials -/

section KaehlerLieDeriv

variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] [Algebra k S] [Algebra R S]

/-- Auxiliary `k`-linear map `(S →₀ S) →ₗ[k] Ω[S⁄R]` sending `single x c` to
`δ c • D R S x + c • D R S (δ x)`. -/
private noncomputable def preKaehlerLieDeriv (R : Type*) [CommRing R] [Algebra R S]
    (δ : Derivation k S S) : (S →₀ S) →ₗ[k] Ω[S⁄R] :=
  Finsupp.lsum k fun x : S ↦
    ((LinearMap.lsmul S Ω[S⁄R]).restrictScalars k).flip (KaehlerDifferential.D R S x) ∘ₗ
      δ.toLinearMap +
      ((LinearMap.lsmul S Ω[S⁄R]).restrictScalars k).flip (KaehlerDifferential.D R S (δ x))

private theorem preKaehlerLieDeriv_single (δ : Derivation k S S) (x c : S) :
    preKaehlerLieDeriv R δ (Finsupp.single x c) =
      δ c • KaehlerDifferential.D R S x + c • KaehlerDifferential.D R S (δ x) := by
  simp [preKaehlerLieDeriv]

private theorem preKaehlerLieDeriv_smul (δ : Derivation k S S) (s : S) (v : S →₀ S) :
    preKaehlerLieDeriv R δ (s • v) =
      s • preKaehlerLieDeriv R δ v +
        δ s • Finsupp.linearCombination S (KaehlerDifferential.D R S) v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v₁ v₂ ih₁ ih₂ =>
    rw [smul_add, map_add, map_add, map_add, smul_add, smul_add, ih₁, ih₂]
    abel
  | single x c =>
    rw [Finsupp.smul_single, smul_eq_mul, preKaehlerLieDeriv_single, preKaehlerLieDeriv_single,
      Finsupp.linearCombination_single, δ.leibniz, add_smul, smul_add]
    simp only [smul_eq_mul, smul_smul, mul_comm c (δ s)]
    abel

private theorem preKaehlerLieDeriv_eq_zero_of_mem_kerTotal (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    {v : S →₀ S} (hv : v ∈ KaehlerDifferential.kerTotal R S) :
    preKaehlerLieDeriv R δ v = 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    rcases hv with (⟨⟨x, y⟩, rfl⟩ | ⟨⟨x, y⟩, rfl⟩) | ⟨r, rfl⟩
    · simp only [map_sub, map_add, preKaehlerLieDeriv_single, Derivation.map_one_eq_zero,
        zero_smul, zero_add, one_smul]
      abel
    · simp only [map_sub, map_add, preKaehlerLieDeriv_single, Derivation.map_one_eq_zero,
        zero_smul, zero_add, one_smul, δ.leibniz, smul_eq_mul, Derivation.leibniz]
      abel
    · simp [preKaehlerLieDeriv_single, hδ r]
  | zero => simp
  | add _ _ _ _ ih₁ ih₂ => rw [map_add, ih₁, ih₂, add_zero]
  | smul s v hv ih =>
    have hker : Finsupp.linearCombination S (KaehlerDifferential.D R S) v = 0 := by
      rwa [← LinearMap.mem_ker, KaehlerDifferential.kerTotal_eq]
    rw [preKaehlerLieDeriv_smul, ih, hker, smul_zero, smul_zero, add_zero]

/-- **Lie derivative on Kähler differentials**: for a `k`-derivation `δ : Derivation k S S` such
that `D R S (δ (algebraMap R S r)) = 0` for all `r : R`, `δ.kaehlerLieDeriv hδ` is the `k`-linear
endomorphism of `Ω[S⁄R]` sending `D R S s` to `D R S (δ s)`. -/
noncomputable def kaehlerLieDeriv (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) :
    Module.End k Ω[S⁄R] :=
  (((KaehlerDifferential.kerTotal R S).restrictScalars k).liftQ (preKaehlerLieDeriv R δ)
    fun v hv ↦ preKaehlerLieDeriv_eq_zero_of_mem_kerTotal δ hδ
      ((Submodule.restrictScalars_mem k _ v).mp hv)).comp
    ((Submodule.Quotient.restrictScalarsEquiv k
        (KaehlerDifferential.kerTotal R S)).symm.toLinearMap.comp
      ((KaehlerDifferential.quotKerTotalEquiv R S).symm.toLinearMap.restrictScalars k))

private theorem kaehlerLieDeriv_linearCombination (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) (w : S →₀ S) :
    δ.kaehlerLieDeriv hδ (Finsupp.linearCombination S (KaehlerDifferential.D R S) w) =
      preKaehlerLieDeriv R δ w := by
  have hw : (KaehlerDifferential.quotKerTotalEquiv R S).symm
      (Finsupp.linearCombination S (KaehlerDifferential.D R S) w) =
      Submodule.Quotient.mk w := by
    apply (KaehlerDifferential.quotKerTotalEquiv R S).injective
    rw [LinearEquiv.apply_symm_apply]
    rfl
  simp only [kaehlerLieDeriv, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_toLinearMap, hw, Submodule.Quotient.restrictScalarsEquiv_symm_mk]
  exact Submodule.liftQ_apply _ _ w

/-- On exact Kähler differentials `D R S s`, `δ.kaehlerLieDeriv hδ` acts by `D R S (δ s)`. -/
@[simp]
theorem kaehlerLieDeriv_D (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) (s : S) :
    δ.kaehlerLieDeriv hδ (KaehlerDifferential.D R S s) = KaehlerDifferential.D R S (δ s) := by
  rw [← one_smul S (KaehlerDifferential.D R S s), ← Finsupp.linearCombination_single,
    kaehlerLieDeriv_linearCombination, preKaehlerLieDeriv_single, Derivation.map_one_eq_zero,
    zero_smul, zero_add, one_smul]

/-- **Leibniz rule for scalar multiplication on `Ω[S⁄R]`**:
`δ.kaehlerLieDeriv hδ (s • ω) = δ s • ω + s • δ.kaehlerLieDeriv hδ ω`. -/
theorem kaehlerLieDeriv_smul (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    (s : S) (ω : Ω[S⁄R]) :
    δ.kaehlerLieDeriv hδ (s • ω) = δ s • ω + s • δ.kaehlerLieDeriv hδ ω := by
  obtain ⟨v, rfl⟩ := KaehlerDifferential.linearCombination_surjective R S ω
  rw [← LinearMap.map_smul, kaehlerLieDeriv_linearCombination, kaehlerLieDeriv_linearCombination,
    preKaehlerLieDeriv_smul, add_comm]

/-- **Necessary and sufficient condition for lifting a `k`-derivation of `S` to `Ω[S⁄R]`**:
there exists a `k`-linear endomorphism `L` of `Ω[S⁄R]` satisfying `L (D R S s) = D R S (δ s)` for
all `s : S` if and only if `D R S (δ (algebraMap R S r)) = 0` for all `r : R`. -/
theorem exists_kaehlerLieDeriv_iff (δ : Derivation k S S) :
    (∃ L : Module.End k Ω[S⁄R],
      ∀ s : S, L (KaehlerDifferential.D R S s) = KaehlerDifferential.D R S (δ s)) ↔
      ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0 :=
  ⟨fun ⟨L, hL⟩ r ↦ by rw [← hL, Derivation.map_algebraMap, map_zero],
    fun hδ ↦ ⟨δ.kaehlerLieDeriv hδ, δ.kaehlerLieDeriv_D hδ⟩⟩

/-- Uniqueness of `δ.kaehlerLieDeriv hδ` from its action on `D R S s` and the `S`-module Leibniz
rule. -/
theorem kaehlerLieDeriv_unique (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    {L : Module.End k Ω[S⁄R]}
    (hD : ∀ s : S, L (KaehlerDifferential.D R S s) = KaehlerDifferential.D R S (δ s))
    (hsmul : ∀ (s : S) (ω : Ω[S⁄R]), L (s • ω) = δ s • ω + s • L ω) :
    L = δ.kaehlerLieDeriv hδ := by
  refine LinearMap.ext fun ω ↦ ?_
  induction (KaehlerDifferential.span_range_derivation R S ▸ Submodule.mem_top :
      ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S))) using
      Submodule.span_induction with
  | mem _ hω =>
    obtain ⟨s, rfl⟩ := hω
    rw [hD, kaehlerLieDeriv_D]
  | zero => simp
  | add _ _ _ _ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂]
  | smul s ω _ ih => rw [hsmul, kaehlerLieDeriv_smul, ih]

/-- `kaehlerLieDeriv` is additive in the derivation `δ`. -/
theorem kaehlerLieDeriv_add {δ₁ δ₂ : Derivation k S S}
    (h₁ : ∀ r : R, KaehlerDifferential.D R S (δ₁ (algebraMap R S r)) = 0)
    (h₂ : ∀ r : R, KaehlerDifferential.D R S (δ₂ (algebraMap R S r)) = 0) :
    (δ₁ + δ₂).kaehlerLieDeriv (fun r ↦ by simp [h₁ r, h₂ r]) =
      δ₁.kaehlerLieDeriv h₁ + δ₂.kaehlerLieDeriv h₂ := by
  refine ((δ₁ + δ₂).kaehlerLieDeriv_unique _ (fun s ↦ by simp) fun s ω ↦ ?_).symm
  simp only [LinearMap.add_apply, kaehlerLieDeriv_smul, _root_.add_apply, add_smul, smul_add]
  abel

/-- `kaehlerLieDeriv` maps the zero derivation to zero. -/
@[simp]
theorem kaehlerLieDeriv_zero :
    (0 : Derivation k S S).kaehlerLieDeriv (fun _ : R ↦ by simp) = 0 :=
  ((0 : Derivation k S S).kaehlerLieDeriv_unique (fun _ : R ↦ by simp)
    (fun _ ↦ by simp) (fun _ _ ↦ by simp)).symm

/-- Every `R`-linear derivation `δ : Derivation R S S` automatically satisfies the lift condition
`D R S (δ (algebraMap R S r)) = 0`. -/
theorem D_apply_algebraMap_eq_zero (δ : Derivation R S S) (r : R) :
    KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0 := by
  rw [Derivation.map_algebraMap, map_zero]

/-- If `δ₁, δ₂ : Derivation k S S` satisfy the lift condition for `Ω[S⁄R]`, so does their
commutator `⁅δ₁, δ₂⁆`. -/
theorem D_commutator_algebraMap_eq_zero {δ₁ δ₂ : Derivation k S S}
    (h₁ : ∀ r : R, KaehlerDifferential.D R S (δ₁ (algebraMap R S r)) = 0)
    (h₂ : ∀ r : R, KaehlerDifferential.D R S (δ₂ (algebraMap R S r)) = 0) (r : R) :
    KaehlerDifferential.D R S (⁅δ₁, δ₂⁆ (algebraMap R S r)) = 0 := by
  rw [Derivation.commutator_apply, map_sub, ← δ₁.kaehlerLieDeriv_D h₁ (δ₂ _),
    ← δ₂.kaehlerLieDeriv_D h₂ (δ₁ _), h₂ r, h₁ r, map_zero, map_zero, sub_self]

/-- Any compatible derivation couple `c : Derivation.couple k R S` satisfies the lift condition for
`Ω[S⁄R]` because `c.1.1` preserves the image of `algebraMap R S`. -/
theorem Compatible.D_apply_algebraMap_eq_zero [Algebra k R] [IsScalarTower k R S]
    (c : Derivation.couple k R S) (r : R) :
    KaehlerDifferential.D R S (c.1.1 (algebraMap R S r)) = 0 := by
  have hc : c.1.1 (algebraMap R S r) = algebraMap R S (c.1.2 r) := Compatible.apply c r
  rw [hc, Derivation.map_algebraMap]

end KaehlerLieDeriv

/-! ### Lie derivative on the algebraic de Rham complex -/

section DeRhamLieDeriv

variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] [Algebra k S] [Algebra R S]

/-- Auxiliary even dual-number algebra over `S` with carrier `A × A` and multiplication
`(a, a') * (b, b') = (a * b, a' * b + a * b')`. -/
@[ext]
private structure EvenDual (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] where
  fst : ExteriorAlgebra S Ω[S⁄R]
  snd : ExteriorAlgebra S Ω[S⁄R]

private noncomputable instance : Zero (EvenDual R S) := ⟨⟨0, 0⟩⟩
private noncomputable instance : One (EvenDual R S) := ⟨⟨1, 0⟩⟩
private noncomputable instance : Add (EvenDual R S) := ⟨fun x y ↦ ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
private noncomputable instance : Neg (EvenDual R S) := ⟨fun x ↦ ⟨-x.fst, -x.snd⟩⟩
private noncomputable instance : Sub (EvenDual R S) := ⟨fun x y ↦ ⟨x.fst - y.fst, x.snd - y.snd⟩⟩
private noncomputable instance : SMul ℕ (EvenDual R S) := ⟨fun n x ↦ ⟨n • x.fst, n • x.snd⟩⟩
private noncomputable instance : SMul ℤ (EvenDual R S) := ⟨fun z x ↦ ⟨z • x.fst, z • x.snd⟩⟩
private noncomputable instance : Mul (EvenDual R S) :=
  ⟨fun x y ↦ ⟨x.fst * y.fst, x.snd * y.fst + x.fst * y.snd⟩⟩

@[simp] private theorem EvenDual.zero_fst : (0 : EvenDual R S).fst = 0 := rfl
@[simp] private theorem EvenDual.zero_snd : (0 : EvenDual R S).snd = 0 := rfl
@[simp] private theorem EvenDual.one_fst : (1 : EvenDual R S).fst = 1 := rfl
@[simp] private theorem EvenDual.one_snd : (1 : EvenDual R S).snd = 0 := rfl
@[simp] private theorem EvenDual.add_fst (x y : EvenDual R S) : (x + y).fst = x.fst + y.fst := rfl
@[simp] private theorem EvenDual.add_snd (x y : EvenDual R S) : (x + y).snd = x.snd + y.snd := rfl
@[simp] private theorem EvenDual.neg_fst (x : EvenDual R S) : (-x).fst = -x.fst := rfl
@[simp] private theorem EvenDual.neg_snd (x : EvenDual R S) : (-x).snd = -x.snd := rfl
@[simp] private theorem EvenDual.sub_fst (x y : EvenDual R S) : (x - y).fst = x.fst - y.fst := rfl
@[simp] private theorem EvenDual.sub_snd (x y : EvenDual R S) : (x - y).snd = x.snd - y.snd := rfl
@[simp] private theorem EvenDual.nsmul_fst (n : ℕ) (x : EvenDual R S) : (n • x).fst = n • x.fst :=
  rfl
@[simp] private theorem EvenDual.nsmul_snd (n : ℕ) (x : EvenDual R S) : (n • x).snd = n • x.snd :=
  rfl
@[simp] private theorem EvenDual.zsmul_fst (z : ℤ) (x : EvenDual R S) : (z • x).fst = z • x.fst :=
  rfl
@[simp] private theorem EvenDual.zsmul_snd (z : ℤ) (x : EvenDual R S) : (z • x).snd = z • x.snd :=
  rfl
@[simp] private theorem EvenDual.mul_fst (x y : EvenDual R S) : (x * y).fst = x.fst * y.fst := rfl
@[simp] private theorem EvenDual.mul_snd (x y : EvenDual R S) :
    (x * y).snd = x.snd * y.fst + x.fst * y.snd := rfl

private noncomputable instance : Ring (EvenDual R S) where
  add_assoc x y z := by ext <;> exact add_assoc _ _ _
  zero_add x := by ext <;> exact zero_add _
  add_zero x := by ext <;> exact add_zero _
  nsmul n x := n • x
  nsmul_zero x := by ext <;> exact zero_smul ℕ _
  nsmul_succ n x := by ext <;> exact succ_nsmul _ n
  zsmul z x := z • x
  zsmul_zero' x := by ext <;> exact zero_smul ℤ _
  zsmul_succ' n x := by ext <;> exact SubNegMonoid.zsmul_succ' n _
  zsmul_neg' n x := by ext <;> exact SubNegMonoid.zsmul_neg' n _
  neg_add_cancel x := by ext <;> exact neg_add_cancel _
  add_comm x y := by ext <;> exact add_comm _ _
  sub_eq_add_neg x y := by ext <;> exact sub_eq_add_neg _ _
  left_distrib x y z := by
    ext <;> simp only [EvenDual.mul_fst, EvenDual.mul_snd, EvenDual.add_fst, EvenDual.add_snd,
      mul_add]
    abel
  right_distrib x y z := by
    ext <;> simp only [EvenDual.mul_fst, EvenDual.mul_snd, EvenDual.add_fst, EvenDual.add_snd,
      add_mul]
    abel
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp
  mul_assoc x y z := by
    ext <;> simp only [EvenDual.mul_fst, EvenDual.mul_snd, add_mul, mul_add, mul_assoc]
    abel
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp

private noncomputable def evenDualRingHom (R : Type*) [CommRing R] [Algebra R S]
    (δ : Derivation k S S) : S →+* EvenDual R S where
  toFun s := ⟨algebraMap S _ s, algebraMap S _ (δ s)⟩
  map_one' := by ext <;> simp
  map_mul' s t := by
    ext
    · exact map_mul _ s t
    · simp only [EvenDual.mul_snd, δ.leibniz, map_add, smul_eq_mul, map_mul]
      rw [Algebra.commutes t, add_comm]
  map_zero' := by ext <;> simp
  map_add' s t := by ext <;> simp

@[instance_reducible]
private noncomputable def evenDualAlgebra (R : Type*) [CommRing R] [Algebra R S]
    (δ : Derivation k S S) : Algebra S (EvenDual R S) :=
  (evenDualRingHom R δ).toAlgebra' fun s z ↦ by
    ext
    · exact Algebra.commutes s z.fst
    · simp only [EvenDual.mul_snd, evenDualRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
      rw [Algebra.commutes (δ s) z.fst, Algebra.commutes s z.snd, add_comm]

private noncomputable def evenDualGenerator (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) :
    letI : Algebra S (EvenDual R S) := evenDualAlgebra R δ
    Ω[S⁄R] →ₗ[S] EvenDual R S :=
  letI : Algebra S (EvenDual R S) := evenDualAlgebra R δ
  { toFun := fun ω ↦ ⟨ExteriorAlgebra.ι S ω, ExteriorAlgebra.ι S (δ.kaehlerLieDeriv hδ ω)⟩
    map_add' := fun ω₁ ω₂ ↦ by ext <;> simp
    map_smul' := fun s ω ↦ by
      ext
      · -- Scalar multiplication by `s` on the first factor of `EvenDual` is `algebraMap S _ s * _`.
        change ExteriorAlgebra.ι S (s • ω) = algebraMap S _ s * ExteriorAlgebra.ι S ω
        rw [LinearMap.map_smul, Algebra.smul_def]
      · -- Scalar multiplication by `s` on `EvenDual` acts via `(s, δ s)`.
        change ExteriorAlgebra.ι S (δ.kaehlerLieDeriv hδ (s • ω)) =
          algebraMap S _ (δ s) * ExteriorAlgebra.ι S ω +
            algebraMap S _ s * ExteriorAlgebra.ι S (δ.kaehlerLieDeriv hδ ω)
        rw [kaehlerLieDeriv_smul, map_add, LinearMap.map_smul, LinearMap.map_smul,
          Algebra.smul_def, Algebra.smul_def] }

@[simp] private theorem evenDualGenerator_fst (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) (ω : Ω[S⁄R]) :
    (evenDualGenerator δ hδ ω).fst = ExteriorAlgebra.ι S ω := rfl
@[simp] private theorem evenDualGenerator_snd (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) (ω : Ω[S⁄R]) :
    (evenDualGenerator δ hδ ω).snd = ExteriorAlgebra.ι S (δ.kaehlerLieDeriv hδ ω) := rfl

private noncomputable def evenDualLift (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) :
    letI : Algebra S (EvenDual R S) := evenDualAlgebra R δ
    ExteriorAlgebra S Ω[S⁄R] →ₐ[S] EvenDual R S :=
  letI : Algebra S (EvenDual R S) := evenDualAlgebra R δ
  ExteriorAlgebra.lift S ⟨evenDualGenerator δ hδ, fun ω ↦ by
    ext
    · exact ExteriorAlgebra.ι_sq_zero ω
    · simp only [EvenDual.mul_snd, EvenDual.zero_snd, evenDualGenerator_fst, evenDualGenerator_snd]
      exact ExteriorAlgebra.ι_add_mul_swap _ _⟩

private theorem evenDualLift_fst (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    (x : ExteriorAlgebra S Ω[S⁄R]) :
    (evenDualLift δ hδ x).fst = x := by
  let _ : Algebra S (EvenDual R S) := evenDualAlgebra R δ
  let fstHom : EvenDual R S →ₐ[S] ExteriorAlgebra S Ω[S⁄R] :=
    { toFun := EvenDual.fst
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  have h : fstHom.comp (evenDualLift δ hδ) = AlgHom.id S _ :=
    ExteriorAlgebra.hom_ext <| LinearMap.ext fun ω ↦ by
      simp only [AlgHom.comp_toLinearMap, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        evenDualLift, ExteriorAlgebra.lift_ι_apply, AlgHom.id_apply]
      rfl
  exact AlgHom.congr_fun h x

/-- **Lie derivative on the algebraic de Rham complex**: for a `k`-derivation `δ : Derivation k S S`
satisfying `∀ r : R, D R S (δ (algebraMap R S r)) = 0`, `δ.deRhamLieDeriv hδ` is the `k`-linear
derivation of `ExteriorAlgebra S Ω[S⁄R]` extending `δ` in degree zero and `δ.kaehlerLieDeriv hδ` in
degree one. -/
noncomputable def deRhamLieDeriv (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) :
    Module.End k (ExteriorAlgebra S Ω[S⁄R]) :=
  letI : Algebra S (EvenDual R S) := evenDualAlgebra R δ
  { toFun := fun x ↦ (evenDualLift δ hδ x).snd
    map_add' := fun x y ↦ congrArg EvenDual.snd (map_add (evenDualLift δ hδ) x y)
    map_smul' := fun c x ↦ by
      rw [← IsScalarTower.algebraMap_smul S c x, AlgHom.map_smul_of_tower]
      -- In `evenDualAlgebra R δ`, `algebraMap k S c • z` multiplies `z` on the left by `(c, δ c)`.
      change algebraMap S _ (δ (algebraMap k S c)) * (evenDualLift δ hδ x).fst +
          algebraMap S _ (algebraMap k S c) * (evenDualLift δ hδ x).snd =
        c • (evenDualLift δ hδ x).snd
      rw [Derivation.map_algebraMap, map_zero, zero_mul, zero_add, ← Algebra.smul_def,
        IsScalarTower.algebraMap_smul] }

private theorem deRhamLieDeriv_apply (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    (x : ExteriorAlgebra S Ω[S⁄R]) :
    δ.deRhamLieDeriv hδ x = (evenDualLift δ hδ x).snd := rfl

/-- On degree-zero elements `algebraMap S _ s`, `δ.deRhamLieDeriv hδ` acts by `δ`. -/
@[simp]
theorem deRhamLieDeriv_algebraMap (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) (s : S) :
    δ.deRhamLieDeriv hδ (algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s) =
      algebraMap S (ExteriorAlgebra S Ω[S⁄R]) (δ s) := by
  let _ : Algebra S (EvenDual R S) := evenDualAlgebra R δ
  rw [deRhamLieDeriv_apply, AlgHom.commutes]
  rfl

/-- `δ.deRhamLieDeriv hδ` annihilates `1`. -/
@[simp]
theorem deRhamLieDeriv_one (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) :
    δ.deRhamLieDeriv hδ 1 = 0 := by
  rw [← map_one (algebraMap S (ExteriorAlgebra S Ω[S⁄R])), deRhamLieDeriv_algebraMap,
    Derivation.map_one_eq_zero, map_zero]

/-- On `1`-forms `ι ω`, `δ.deRhamLieDeriv hδ` acts through `δ.kaehlerLieDeriv hδ`. -/
@[simp]
theorem deRhamLieDeriv_ι (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) (ω : Ω[S⁄R]) :
    δ.deRhamLieDeriv hδ (ExteriorAlgebra.ι S ω) =
      ExteriorAlgebra.ι S (δ.kaehlerLieDeriv hδ ω) := by
  let _ : Algebra S (EvenDual R S) := evenDualAlgebra R δ
  rw [deRhamLieDeriv_apply, evenDualLift, ExteriorAlgebra.lift_ι_apply, evenDualGenerator_snd]

/-- On exact `1`-forms `ι (D R S s)`, `δ.deRhamLieDeriv hδ` sends `ι (D s)` to `ι (D (δ s))`. -/
theorem deRhamLieDeriv_ι_D (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) (s : S) :
    δ.deRhamLieDeriv hδ (ExteriorAlgebra.ι S (KaehlerDifferential.D R S s)) =
      ExteriorAlgebra.ι S (KaehlerDifferential.D R S (δ s)) := by
  simp

/-- **Even Leibniz rule** for `δ.deRhamLieDeriv hδ` on exterior products. -/
theorem deRhamLieDeriv_mul (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    (x y : ExteriorAlgebra S Ω[S⁄R]) :
    δ.deRhamLieDeriv hδ (x * y) =
      δ.deRhamLieDeriv hδ x * y + x * δ.deRhamLieDeriv hδ y := by
  let _ : Algebra S (EvenDual R S) := evenDualAlgebra R δ
  rw [deRhamLieDeriv_apply, map_mul, EvenDual.mul_snd, evenDualLift_fst, evenDualLift_fst,
    ← deRhamLieDeriv_apply, ← deRhamLieDeriv_apply]

/-- `δ.deRhamLieDeriv hδ` belongs to the Lie algebra of `k`-derivations of
`ExteriorAlgebra S Ω[S⁄R]`. -/
theorem deRhamLieDeriv_mem_derivationLieAlgebra (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) :
    δ.deRhamLieDeriv hδ ∈ TauCeti.derivationLieAlgebra k (ExteriorAlgebra S Ω[S⁄R]) :=
  TauCeti.mem_derivationLieAlgebra.mpr (δ.deRhamLieDeriv_mul hδ)

/-- Scalar multiplication by `s : S` obeys `L_δ (s • x) = δ s • x + s • L_δ x`. -/
theorem deRhamLieDeriv_smul (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    (s : S) (x : ExteriorAlgebra S Ω[S⁄R]) :
    δ.deRhamLieDeriv hδ (s • x) = δ s • x + s • δ.deRhamLieDeriv hδ x := by
  rw [Algebra.smul_def, deRhamLieDeriv_mul, deRhamLieDeriv_algebraMap, ← Algebra.smul_def,
    ← Algebra.smul_def]

/-- `δ.deRhamLieDeriv hδ` preserves each exterior power `⋀[S]^n Ω[S⁄R]`. -/
theorem deRhamLieDeriv_mem_exteriorPower (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    {n : ℕ} {x : ExteriorAlgebra S Ω[S⁄R]} (hx : x ∈ ⋀[S]^n Ω[S⁄R]) :
    δ.deRhamLieDeriv hδ x ∈ ⋀[S]^n Ω[S⁄R] := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap s =>
    rw [deRhamLieDeriv_algebraMap, _root_.ExteriorAlgebra.exteriorPower, pow_zero]
    exact Submodule.algebraMap_mem (δ s)
  | add x y i _ _ ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨ω, rfl⟩ := hm
    rw [deRhamLieDeriv_mul, deRhamLieDeriv_ι, Nat.succ_eq_one_add]
    exact add_mem
      (SetLike.mul_mem_graded (TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one _) hx)
      (SetLike.mul_mem_graded (TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one _) ih)

/-- `δ.deRhamLieDeriv hδ` preserves each homogeneous piece `grading R S p`. -/
theorem deRhamLieDeriv_mem_grading (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    {p : ℤ} {x : ExteriorAlgebra S Ω[S⁄R]} (hx : x ∈ grading R S p) :
    δ.deRhamLieDeriv hδ x ∈ grading R S p := by
  rcases lt_or_ge p 0 with hp | hp
  · rw [grading_of_neg hp, Submodule.mem_bot] at hx
    rw [hx, map_zero]
    exact zero_mem _
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    rw [mem_grading_natCast] at hx ⊢
    exact δ.deRhamLieDeriv_mem_exteriorPower hδ hx

/-- `δ.deRhamLieDeriv hδ` commutes with the grade involution on `ExteriorAlgebra S Ω[S⁄R]`. -/
theorem deRhamLieDeriv_involute (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    (x : ExteriorAlgebra S Ω[S⁄R]) :
    δ.deRhamLieDeriv hδ (involute (Q := (0 : QuadraticForm S Ω[S⁄R])) x) =
      involute (Q := (0 : QuadraticForm S Ω[S⁄R])) (δ.deRhamLieDeriv hδ x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap s => rw [AlgHom.commutes, deRhamLieDeriv_algebraMap, AlgHom.commutes]
  | ι ω => rw [involute_ι, map_neg, deRhamLieDeriv_ι, involute_ι]
  | mul x y ihx ihy =>
    rw [map_mul, deRhamLieDeriv_mul, ihx, ihy, deRhamLieDeriv_mul, map_add, map_mul, map_mul]
  | add x y ihx ihy =>
    rw [map_add, map_add, ihx, ihy, ← map_add involute, ← map_add (δ.deRhamLieDeriv hδ)]

/-- **The exterior derivative commutes with the Lie derivative** on `ExteriorAlgebra S Ω[S⁄R]`. -/
theorem extDeriv_deRhamLieDeriv (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    (x : ExteriorAlgebra S Ω[S⁄R]) :
    extDeriv R S (δ.deRhamLieDeriv hδ x) = δ.deRhamLieDeriv hδ (extDeriv R S x) := by
  have hmul : ∀ a b : ExteriorAlgebra S Ω[S⁄R],
      extDeriv R S (δ.deRhamLieDeriv hδ a) = δ.deRhamLieDeriv hδ (extDeriv R S a) →
      extDeriv R S (δ.deRhamLieDeriv hδ b) = δ.deRhamLieDeriv hδ (extDeriv R S b) →
      extDeriv R S (δ.deRhamLieDeriv hδ (a * b)) =
        δ.deRhamLieDeriv hδ (extDeriv R S (a * b)) := by
    intro a b iha ihb
    rw [deRhamLieDeriv_mul, map_add, extDeriv_mul, extDeriv_mul, iha, ihb,
      ← deRhamLieDeriv_involute, extDeriv_mul, map_add, deRhamLieDeriv_mul, deRhamLieDeriv_mul]
    abel
  induction x using CliffordAlgebra.induction with
  | algebraMap s =>
    rw [deRhamLieDeriv_algebraMap, extDeriv_algebraMap, extDeriv_algebraMap, deRhamLieDeriv_ι_D]
  | ι ω =>
    induction (KaehlerDifferential.span_range_derivation R S ▸ Submodule.mem_top :
        ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S))) using
        Submodule.span_induction with
    | mem _ hω =>
      obtain ⟨s, rfl⟩ := hω
      rw [deRhamLieDeriv_ι_D, extDeriv_ι_D, extDeriv_ι_D, map_zero]
    | zero => simp
    | add _ _ _ _ ih₁ ih₂ => rw [map_add, map_add, map_add, map_add, map_add, ih₁, ih₂]
    | smul s ω _ ih =>
      rw [LinearMap.map_smul, Algebra.smul_def]
      exact hmul _ _ (by rw [deRhamLieDeriv_algebraMap, extDeriv_algebraMap, extDeriv_algebraMap,
        deRhamLieDeriv_ι_D]) ih
  | mul x y ihx ihy => exact hmul x y ihx ihy
  | add x y ihx ihy => rw [map_add, map_add, ihx, ihy, ← map_add (δ.deRhamLieDeriv hδ),
      ← map_add (extDeriv R S)]

/-- Pointwise commutation of `extDeriv R S` and `δ.deRhamLieDeriv hδ`, packaged as
`Function.Commute`. -/
theorem commute_extDeriv_deRhamLieDeriv (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) :
    Function.Commute (extDeriv R S) (δ.deRhamLieDeriv hδ) :=
  δ.extDeriv_deRhamLieDeriv hδ

/-- **Uniqueness of the Lie derivative on the algebraic de Rham complex**: `δ.deRhamLieDeriv hδ`
is the unique `k`-linear algebra derivation of `ExteriorAlgebra S Ω[S⁄R]` that extends `δ` on `S`
and commutes with `extDeriv R S`. -/
theorem deRhamLieDeriv_unique (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    {L : Module.End k (ExteriorAlgebra S Ω[S⁄R])}
    (hder : L ∈ TauCeti.derivationLieAlgebra k (ExteriorAlgebra S Ω[S⁄R]))
    (halg : ∀ s : S,
      L (algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s) =
        algebraMap S (ExteriorAlgebra S Ω[S⁄R]) (δ s))
    (hcomm : ∀ x : ExteriorAlgebra S Ω[S⁄R], extDeriv R S (L x) = L (extDeriv R S x)) :
    L = δ.deRhamLieDeriv hδ := by
  have hleib := TauCeti.mem_derivationLieAlgebra.mp hder
  refine LinearMap.ext fun x ↦ ?_
  induction x using CliffordAlgebra.induction with
  | algebraMap s => rw [halg, deRhamLieDeriv_algebraMap]
  | ι ω =>
    induction (KaehlerDifferential.span_range_derivation R S ▸ Submodule.mem_top :
        ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S))) using
        Submodule.span_induction with
    | mem _ hω =>
      obtain ⟨s, rfl⟩ := hω
      rw [← extDeriv_algebraMap, ← hcomm, halg, extDeriv_algebraMap, extDeriv_algebraMap,
        deRhamLieDeriv_ι_D]
    | zero => simp
    | add _ _ _ _ ih₁ ih₂ => rw [map_add, map_add, map_add, ih₁, ih₂]
    | smul s ω _ ih =>
      rw [LinearMap.map_smul, Algebra.smul_def, hleib, deRhamLieDeriv_mul, halg,
        deRhamLieDeriv_algebraMap, ih]
  | mul x y ihx ihy => rw [hleib, deRhamLieDeriv_mul, ihx, ihy]
  | add x y ihx ihy => rw [map_add, map_add, ihx, ihy]

/-- `deRhamLieDeriv` is additive in the derivation `δ`. -/
theorem deRhamLieDeriv_add {δ₁ δ₂ : Derivation k S S}
    (h₁ : ∀ r : R, KaehlerDifferential.D R S (δ₁ (algebraMap R S r)) = 0)
    (h₂ : ∀ r : R, KaehlerDifferential.D R S (δ₂ (algebraMap R S r)) = 0) :
    (δ₁ + δ₂).deRhamLieDeriv (fun r ↦ by simp [h₁ r, h₂ r]) =
      δ₁.deRhamLieDeriv h₁ + δ₂.deRhamLieDeriv h₂ := by
  symm
  refine deRhamLieDeriv_unique (δ₁ + δ₂) _
    (Submodule.add_mem _ (δ₁.deRhamLieDeriv_mem_derivationLieAlgebra h₁)
      (δ₂.deRhamLieDeriv_mem_derivationLieAlgebra h₂))
    (fun s ↦ by simp)
    fun x ↦ ?_
  rw [LinearMap.add_apply, map_add, extDeriv_deRhamLieDeriv, extDeriv_deRhamLieDeriv,
    LinearMap.add_apply]

/-- `deRhamLieDeriv` maps the zero derivation to zero. -/
@[simp]
theorem deRhamLieDeriv_zero :
    (0 : Derivation k S S).deRhamLieDeriv (fun _ : R ↦ by simp) = 0 := by
  symm
  exact deRhamLieDeriv_unique 0 (fun _ : R ↦ by simp) (Submodule.zero_mem _)
    (fun _ ↦ by simp) (fun _ ↦ by simp)

/-- Scalar multiplication by `a : k` commutes with `deRhamLieDeriv` in a scalar tower
`k → R → S`. -/
theorem smul_deRhamLieDeriv [Algebra k R] [IsScalarTower k R S] (a : k) (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    (haδ : ∀ r : R, KaehlerDifferential.D R S ((a • δ) (algebraMap R S r)) = 0 := fun r ↦ by
      rw [_root_.smul_apply, ← IsScalarTower.algebraMap_smul R a, map_smul, hδ, smul_zero]) :
    (a • δ).deRhamLieDeriv haδ = a • δ.deRhamLieDeriv hδ := by
  have hsmul (y : ExteriorAlgebra S Ω[S⁄R]) : a • y = algebraMap k R a • y := by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply k S (ExteriorAlgebra S Ω[S⁄R]),
      IsScalarTower.algebraMap_apply k R S,
      ← IsScalarTower.algebraMap_apply R S (ExteriorAlgebra S Ω[S⁄R]), ← Algebra.smul_def]
  symm
  refine deRhamLieDeriv_unique (a • δ) haδ
    (Submodule.smul_mem _ a (δ.deRhamLieDeriv_mem_derivationLieAlgebra hδ))
    (fun s ↦ ?_) (fun x ↦ ?_)
  · rw [LinearMap.smul_apply, δ.deRhamLieDeriv_algebraMap hδ, _root_.smul_apply,
      Algebra.smul_def, IsScalarTower.algebraMap_apply k S (ExteriorAlgebra S Ω[S⁄R]),
      ← map_mul, ← Algebra.smul_def]
  · rw [LinearMap.smul_apply, hsmul, _root_.map_smul, ← hsmul, δ.extDeriv_deRhamLieDeriv hδ,
      LinearMap.smul_apply]

/-- **Lie bracket preservation (`L_{⁅δ₁, δ₂⁆} = [L_{δ₁}, L_{δ₂}]`)**: the Lie derivative of a
commutator of `k`-derivations of `S` is the commutator of their Lie derivatives on
`ExteriorAlgebra S Ω[S⁄R]`. -/
theorem deRhamLieDeriv_commutator {δ₁ δ₂ : Derivation k S S}
    (h₁ : ∀ r : R, KaehlerDifferential.D R S (δ₁ (algebraMap R S r)) = 0)
    (h₂ : ∀ r : R, KaehlerDifferential.D R S (δ₂ (algebraMap R S r)) = 0) :
    (⁅δ₁, δ₂⁆).deRhamLieDeriv (D_commutator_algebraMap_eq_zero h₁ h₂) =
      (δ₁.deRhamLieDeriv h₁).comp (δ₂.deRhamLieDeriv h₂) -
        (δ₂.deRhamLieDeriv h₂).comp (δ₁.deRhamLieDeriv h₁) := by
  let L₁ : TauCeti.derivationLieAlgebra k (ExteriorAlgebra S Ω[S⁄R]) :=
    ⟨δ₁.deRhamLieDeriv h₁, δ₁.deRhamLieDeriv_mem_derivationLieAlgebra h₁⟩
  let L₂ : TauCeti.derivationLieAlgebra k (ExteriorAlgebra S Ω[S⁄R]) :=
    ⟨δ₂.deRhamLieDeriv h₂, δ₂.deRhamLieDeriv_mem_derivationLieAlgebra h₂⟩
  have hbr : (⁅L₁, L₂⁆ : TauCeti.derivationLieAlgebra k (ExteriorAlgebra S Ω[S⁄R])).1 =
      (δ₁.deRhamLieDeriv h₁).comp (δ₂.deRhamLieDeriv h₂) -
        (δ₂.deRhamLieDeriv h₂).comp (δ₁.deRhamLieDeriv h₁) := rfl
  rw [← hbr]
  symm
  refine deRhamLieDeriv_unique ⁅δ₁, δ₂⁆ _ ⁅L₁, L₂⁆.2 (fun s ↦ ?_) (fun x ↦ ?_)
  · rw [hbr, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      deRhamLieDeriv_algebraMap, deRhamLieDeriv_algebraMap, deRhamLieDeriv_algebraMap,
      deRhamLieDeriv_algebraMap, Derivation.commutator_apply, map_sub]
  · rw [hbr, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, map_sub,
      extDeriv_deRhamLieDeriv, extDeriv_deRhamLieDeriv, extDeriv_deRhamLieDeriv,
      extDeriv_deRhamLieDeriv, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply]

/-- On `Ω[S⁄R]`, the Lie derivative of `⁅δ₁, δ₂⁆` is likewise the commutator of the degree-one Lie
derivatives. -/
theorem kaehlerLieDeriv_commutator {δ₁ δ₂ : Derivation k S S}
    (h₁ : ∀ r : R, KaehlerDifferential.D R S (δ₁ (algebraMap R S r)) = 0)
    (h₂ : ∀ r : R, KaehlerDifferential.D R S (δ₂ (algebraMap R S r)) = 0) :
    (⁅δ₁, δ₂⁆).kaehlerLieDeriv (D_commutator_algebraMap_eq_zero h₁ h₂) =
      (δ₁.kaehlerLieDeriv h₁).comp (δ₂.kaehlerLieDeriv h₂) -
        (δ₂.kaehlerLieDeriv h₂).comp (δ₁.kaehlerLieDeriv h₁) := by
  refine (kaehlerLieDeriv_unique ⁅δ₁, δ₂⁆ _ (fun s ↦ ?_) (fun s ω ↦ ?_)).symm
  · simp [Derivation.commutator_apply]
  · simp only [LinearMap.sub_apply, LinearMap.comp_apply, kaehlerLieDeriv_smul, map_add,
      Derivation.commutator_apply, sub_smul, smul_sub]
    abel

/-- **Commuting derivations lift to commuting Lie derivatives** on the algebraic de Rham complex. -/
theorem commute_deRhamLieDeriv_of_bracket_eq_zero {δ₁ δ₂ : Derivation k S S}
    (h₁ : ∀ r : R, KaehlerDifferential.D R S (δ₁ (algebraMap R S r)) = 0)
    (h₂ : ∀ r : R, KaehlerDifferential.D R S (δ₂ (algebraMap R S r)) = 0)
    (hcomm : ⁅δ₁, δ₂⁆ = 0) :
    Function.Commute (δ₁.deRhamLieDeriv h₁) (δ₂.deRhamLieDeriv h₂) := by
  intro x
  have h := congrFun (congrArg DFunLike.coe (deRhamLieDeriv_commutator h₁ h₂)) x
  have h0 : (⁅δ₁, δ₂⁆).deRhamLieDeriv (D_commutator_algebraMap_eq_zero h₁ h₂) = 0 := by
    symm
    exact deRhamLieDeriv_unique ⁅δ₁, δ₂⁆ _ (Submodule.zero_mem _)
      (fun s ↦ by simp [hcomm]) (fun _ ↦ by simp)
  rw [h0, LinearMap.zero_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.comp_apply] at h
  exact sub_eq_zero.mp h.symm

end DeRhamLieDeriv

/-! ### Cartan's magic formula and the Lie–interior commutator -/

section Cartan

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **Cartan's magic formula** (`L_δ = d ∘ i_δ + i_δ ∘ d`) on the algebraic de Rham complex
`ExteriorAlgebra S Ω[S⁄R]`, as an equality of `R`-linear endomorphisms. -/
theorem deRhamLieDeriv_eq_extDeriv_comp_deRhamInterior_add (δ : Derivation R S S) :
    δ.deRhamLieDeriv δ.D_apply_algebraMap_eq_zero =
      (extDeriv R S).comp (δ.deRhamInterior.restrictScalars R) +
        (δ.deRhamInterior.restrictScalars R).comp (extDeriv R S) := by
  symm
  refine deRhamLieDeriv_unique δ _ ?_ (fun s ↦ ?_) (fun x ↦ ?_)
  · refine TauCeti.mem_derivationLieAlgebra.mpr fun x y ↦ ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
      deRhamInterior_mul, extDeriv_mul, map_add, extDeriv_involute, deRhamInterior_involute,
      involute_involute, neg_mul, add_mul, mul_add]
    abel
  · simp
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
      map_add, extDeriv_extDeriv, map_zero, zero_add, add_zero]

/-- **Cartan's magic formula** applied pointwise:
`δ.deRhamLieDeriv _ x = extDeriv R S (δ.deRhamInterior x) + δ.deRhamInterior (extDeriv R S x)`. -/
theorem deRhamLieDeriv_eq_extDeriv_deRhamInterior_add (δ : Derivation R S S)
    (x : ExteriorAlgebra S Ω[S⁄R]) :
    δ.deRhamLieDeriv δ.D_apply_algebraMap_eq_zero x =
      extDeriv R S (δ.deRhamInterior x) + δ.deRhamInterior (extDeriv R S x) :=
  congr($((deRhamLieDeriv_eq_extDeriv_comp_deRhamInterior_add δ :)) x)

/-- **Cartan commutator between Lie derivative and interior contraction**:
`L_{δ₁} (i_{δ₂} x) - i_{δ₂} (L_{δ₁} x) = i_{⁅δ₁, δ₂⁆} x`. -/
theorem deRhamLieDeriv_deRhamInterior_sub (δ₁ δ₂ : Derivation R S S)
    (x : ExteriorAlgebra S Ω[S⁄R]) :
    δ₁.deRhamLieDeriv δ₁.D_apply_algebraMap_eq_zero (δ₂.deRhamInterior x) -
        δ₂.deRhamInterior (δ₁.deRhamLieDeriv δ₁.D_apply_algebraMap_eq_zero x) =
      (⁅δ₁, δ₂⁆).deRhamInterior x := by
  have hmul : ∀ a b : ExteriorAlgebra S Ω[S⁄R],
      δ₁.deRhamLieDeriv δ₁.D_apply_algebraMap_eq_zero (δ₂.deRhamInterior a) -
          δ₂.deRhamInterior (δ₁.deRhamLieDeriv δ₁.D_apply_algebraMap_eq_zero a) =
        (⁅δ₁, δ₂⁆).deRhamInterior a →
      δ₁.deRhamLieDeriv δ₁.D_apply_algebraMap_eq_zero (δ₂.deRhamInterior b) -
          δ₂.deRhamInterior (δ₁.deRhamLieDeriv δ₁.D_apply_algebraMap_eq_zero b) =
        (⁅δ₁, δ₂⁆).deRhamInterior b →
      δ₁.deRhamLieDeriv δ₁.D_apply_algebraMap_eq_zero (δ₂.deRhamInterior (a * b)) -
          δ₂.deRhamInterior (δ₁.deRhamLieDeriv δ₁.D_apply_algebraMap_eq_zero (a * b)) =
        (⁅δ₁, δ₂⁆).deRhamInterior (a * b) := by
    intro a b iha ihb
    rw [deRhamInterior_mul, map_add, deRhamLieDeriv_mul, deRhamLieDeriv_mul,
      deRhamLieDeriv_involute, deRhamLieDeriv_mul, map_add, deRhamInterior_mul,
      deRhamInterior_mul, deRhamInterior_mul, ← iha, ← ihb, sub_mul, mul_sub]
    abel
  induction x using CliffordAlgebra.induction with
  | algebraMap s => simp
  | ι ω =>
    induction (KaehlerDifferential.span_range_derivation R S ▸ Submodule.mem_top :
        ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S))) using
        Submodule.span_induction with
    | mem _ hω =>
      obtain ⟨s, rfl⟩ := hω
      simp [Derivation.commutator_apply]
    | zero => simp
    | add _ _ _ _ ih₁ ih₂ =>
      simp only [map_add]
      rw [← ih₁, ← ih₂]
      abel
    | smul s ω _ ih =>
      rw [LinearMap.map_smul, Algebra.smul_def]
      exact hmul _ _ (by simp) ih
  | mul x y ihx ihy => exact hmul x y ihx ihy
  | add x y ihx ihy =>
    rw [map_add (δ₂.deRhamInterior), map_add (δ₁.deRhamLieDeriv _),
      map_add (δ₁.deRhamLieDeriv _), map_add (δ₂.deRhamInterior),
      map_add ((⁅δ₁, δ₂⁆).deRhamInterior), ← ihx, ← ihy]
    abel

end Cartan

end Derivation

/-! ### Bundled Lie algebra homomorphisms -/

namespace TauCeti.KaehlerDeRham

section LieHom

/-- **Lie algebra homomorphism** sending an `R`-derivation `δ : Derivation R S S` to its Lie
derivative on the algebraic de Rham algebra `ExteriorAlgebra S Ω[S⁄R]`. -/
noncomputable def lieDerivHom (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    Derivation R S S →ₗ⁅R⁆ TauCeti.derivationLieAlgebra R (ExteriorAlgebra S Ω[S⁄R]) where
  toFun δ := ⟨δ.deRhamLieDeriv δ.D_apply_algebraMap_eq_zero,
    δ.deRhamLieDeriv_mem_derivationLieAlgebra _⟩
  map_add' δ₁ δ₂ := Subtype.ext <| δ₁.deRhamLieDeriv_add _ _
  map_smul' r δ := Subtype.ext <| by
    -- Coercing scalar multiplication from the Lie subalgebra `derivationLieAlgebra` to `Module.End`
    change (r • δ).deRhamLieDeriv _ = r • δ.deRhamLieDeriv _
    exact Derivation.smul_deRhamLieDeriv r δ _
  map_lie' {δ₁ δ₂} := Subtype.ext <| δ₁.deRhamLieDeriv_commutator _ _

/-- Coercing `lieDerivHom R S δ` to `Module.End R (ExteriorAlgebra S Ω[S⁄R])` recovers
`δ.deRhamLieDeriv`. -/
@[simp]
theorem coe_lieDerivHom {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (δ : Derivation R S S) :
    (lieDerivHom R S δ : Module.End R (ExteriorAlgebra S Ω[S⁄R])) =
      δ.deRhamLieDeriv δ.D_apply_algebraMap_eq_zero :=
  (rfl)

/-- **Lie algebra homomorphism** sending a compatible derivation pair
`c : Derivation.couple k R S` in a ring tower `k → R → S` to its Lie derivative on the relative
algebraic de Rham algebra `ExteriorAlgebra S Ω[S⁄R]`. -/
noncomputable def coupleLieDerivHom (k R S : Type*) [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S] :
    Derivation.couple k R S →ₗ⁅k⁆
      TauCeti.derivationLieAlgebra k (ExteriorAlgebra S Ω[S⁄R]) where
  toFun c := ⟨c.1.1.deRhamLieDeriv (Derivation.Compatible.D_apply_algebraMap_eq_zero c),
    c.1.1.deRhamLieDeriv_mem_derivationLieAlgebra _⟩
  map_add' c₁ c₂ := Subtype.ext <| c₁.1.1.deRhamLieDeriv_add _ _
  map_smul' a c := Subtype.ext <| by
    -- Coercing `(•)` from `couple` and `derivationLieAlgebra` to `Derivation` and `Module.End`
    change (a • c.1.1).deRhamLieDeriv _ = a • c.1.1.deRhamLieDeriv _
    exact Derivation.smul_deRhamLieDeriv a c.1.1 _
  map_lie' {c₁ c₂} := Subtype.ext <| c₁.1.1.deRhamLieDeriv_commutator _ _

/-- Coercing `coupleLieDerivHom k R S c` to `Module.End k (ExteriorAlgebra S Ω[S⁄R])` recovers
`c.1.1.deRhamLieDeriv`. -/
@[simp]
theorem coe_coupleLieDerivHom {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
    (c : Derivation.couple k R S) :
    (coupleLieDerivHom k R S c : Module.End k (ExteriorAlgebra S Ω[S⁄R])) =
      c.1.1.deRhamLieDeriv (Derivation.Compatible.D_apply_algebraMap_eq_zero c) :=
  (rfl)

end LieHom

end TauCeti.KaehlerDeRham
