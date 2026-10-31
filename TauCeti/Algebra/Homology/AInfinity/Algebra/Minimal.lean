/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Iso

/-!
# Minimal A∞ algebras

An A∞ algebra is minimal when its unary operation vanishes. Every element is then a cycle and
there are no nonzero boundaries, giving a linear equivalence with its cohomology. Between minimal
algebras, a morphism is a quasi-isomorphism exactly when its linear part is bijective.

## Main definitions

* `TauCeti.AInfinityAlgebra.IsMinimal`: the unary operation vanishes.
* `TauCeti.AInfinityAlgebra.IsMinimal.cohomologyEquiv`: identification with cohomology.
* `TauCeti.AInfinityStrictHom.ofMapMTwo`: between minimal algebras without operations above arity
  two, a degree-preserving linear map preserving `m₂` as a strict morphism.

## Main results

* `TauCeti.AInfinityAlgebra.isMinimal_iff_cycles_eq_top` and
  `TauCeti.AInfinityAlgebra.isMinimal_iff_boundaries_eq_bot`: minimality in terms of cycles and
  boundaries.
* `TauCeti.IsNonUnitalDGAlgebra.isMinimal_toAInfinityAlgebra_iff`: the `A∞` algebra of a DG
  algebra is minimal exactly when the differential vanishes.
* `TauCeti.AInfinityAlgebra.isMinimal_cohomologyAInfinityAlgebra`: the cohomology `A∞` algebra is
  minimal.
* `TauCeti.AInfinityAlgebra.IsMinimal.taylor_coalgHom_of_tprod`: after a coalgebra morphism, the
  Taylor map of a graded algebra only sees the cuts of a word into two blocks.
* `TauCeti.AInfinityHom.isQuasiIso_iff_linearPart_bijective`: between minimal algebras, a
  quasi-isomorphism has bijective linear part.
* `TauCeti.AInfinityHom.isQuasiIso_iff_isIso`: between minimal algebras, the quasi-isomorphisms
  are exactly the `A∞` isomorphisms.
* `TauCeti.AInfinityHom.linearPart_m_two`: between minimal algebras, the linear part of an `A∞`
  morphism is multiplicative.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.3 and 3.4.
* T. Kadeishvili, *The algebraic structure in the homology of an `A(∞)`-algebra*.
-/

public section

namespace TauCeti

universe uR uA uB

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

namespace AInfinityAlgebra

/-! ### Minimal `A∞` algebras -/

/-- An `A∞` algebra is **minimal** when its unary operation `m₁` vanishes. -/
def IsMinimal (𝒜 : AInfinityAlgebra R A) : Prop :=
  𝒜.differential = 0

/-- An `A∞` algebra is minimal exactly when its differential vanishes. -/
theorem isMinimal_def (𝒜 : AInfinityAlgebra R A) : 𝒜.IsMinimal ↔ 𝒜.differential = 0 := Iff.rfl

/-- An `A∞` algebra is minimal exactly when `m₁` vanishes on every input. -/
theorem isMinimal_iff_m_one_eq_zero (𝒜 : AInfinityAlgebra R A) :
    𝒜.IsMinimal ↔ ∀ x : A, 𝒜.m 1 ![x] = 0 := by
  simp only [isMinimal_def, LinearMap.ext_iff, differential_apply, LinearMap.zero_apply]

/-- An `A∞` algebra is minimal exactly when every element is a cycle. -/
theorem isMinimal_iff_cycles_eq_top (𝒜 : AInfinityAlgebra R A) :
    𝒜.IsMinimal ↔ 𝒜.cycles = ⊤ := by
  rw [isMinimal_def, cycles_def, LinearMap.ker_eq_top]

/-- An `A∞` algebra is minimal exactly when zero is its only boundary. -/
theorem isMinimal_iff_boundaries_eq_bot (𝒜 : AInfinityAlgebra R A) :
    𝒜.IsMinimal ↔ 𝒜.boundaries = ⊥ := by
  rw [isMinimal_def, boundaries_def, LinearMap.range_eq_bot]

namespace IsMinimal

variable {𝒜 : AInfinityAlgebra R A}

/-- The unary operation of a minimal `A∞` algebra vanishes. -/
@[simp]
theorem m_one (h : 𝒜.IsMinimal) (x : Fin 1 → A) : 𝒜.m 1 x = 0 := by
  obtain ⟨y, rfl⟩ : ∃ y, x = ![y] := ⟨x 0, funext fun i ↦ by fin_cases i; rfl⟩
  exact (isMinimal_iff_m_one_eq_zero 𝒜).1 h y

open ReducedTensorWords in
/-- The Taylor map of an `A∞` algebra without operations above arity two vanishes on words obtained
by prepending two letters to a nonempty word. -/
private theorem taylor_prepend_prepend (hm : ∀ k, 3 ≤ k → 𝒜.m k = 0) (u v : A)
    (W : ReducedTensorWords R A) : 𝒜.taylor (prepend R A u (prepend R A v W)) = 0 := by
  have h : 𝒜.taylor ∘ₗ prepend R A u ∘ₗ prepend R A v = 0 := by
    refine linearMap_ext R A fun n y ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, prepend_of_tprod, prepend_of_tprod,
      𝒜.taylor_of_tprod, hm _ (by have := n.2; simp only; omega), LinearMap.zero_apply,
      _root_.zero_apply]
  exact LinearMap.congr_fun h W

open ReducedTensorWords in
/-- **The Taylor map of a graded algebra after a coalgebra morphism.**  For a minimal `A∞` algebra
`𝒜` without operations above arity two, the Taylor map after the coalgebra morphism with Taylor
components `f` only sees the cuts of a word into two blocks: on `x₁ ⋯ xₙ` it is the sum over the
cuts of `m₂(τ f(x₁ ⋯ x_d), f(x_{d+1} ⋯ xₙ))`, with `τ` the degree-one Koszul twist carrying the
suspension sign of `m₂`. -/
theorem taylor_coalgHom_of_tprod (h : 𝒜.IsMinimal) (hm : ∀ k, 3 ≤ k → 𝒜.m k = 0)
    (f : ReducedTensorWords R A →ₗ[R] A) {n : ℕ} (hn : 0 < n) (x : Fin n → A) :
    𝒜.taylor (coalgHom R f (of R A ⟨n, hn⟩ (PiTensorProduct.tprod R x))) =
      ∑ d ∈ Finset.range n,
        𝒜.m 2 ![𝒜.grading.koszulTwist 1 (f (subword R x 0 d)), f (subword R x d (n - d))] := by
  rw [of_tprod_eq_subword R hn, coalgHom_subword, map_add, map_sum, taylor_ofLetter, h.m_one,
    zero_add]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [coalgHom_subword, map_add, map_sum, map_add, map_sum, prepend_ofLetter, taylor_of_two,
    zero_add]
  simp [taylor_prepend_prepend hm]

/-- Every element of a minimal `A∞` algebra is a cycle. -/
theorem mem_cycles (h : 𝒜.IsMinimal) (x : A) : x ∈ 𝒜.cycles := by
  rw [AInfinityAlgebra.mem_cycles, h.m_one]

/-- In a minimal `A∞` algebra, the boundaries inside the cycles are trivial. -/
theorem boundariesInCycles_eq_bot (h : 𝒜.IsMinimal) : 𝒜.boundariesInCycles = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [mem_boundariesInCycles, (isMinimal_iff_boundaries_eq_bot 𝒜).1 h,
    Submodule.mem_bot] at hx
  exact Subtype.ext hx

/-- A minimal `A∞` algebra is linearly equivalent to its cohomology: every element is a cycle,
and no nonzero element is a boundary. -/
noncomputable def cohomologyEquiv (h : 𝒜.IsMinimal) : A ≃ₗ[R] 𝒜.Cohomology :=
  𝒜.cohomologyEquivOfCyclesEqTop ((isMinimal_iff_cycles_eq_top 𝒜).1 h)

/-- The identification of a minimal algebra with its cohomology sends an element to its class. -/
@[simp]
theorem cohomologyEquiv_apply (h : 𝒜.IsMinimal) (x : A) :
    h.cohomologyEquiv x = 𝒜.cohomologyClass (h.mem_cycles x) := by
  exact 𝒜.cohomologyEquivOfCyclesEqTop_apply
    ((isMinimal_iff_cycles_eq_top 𝒜).1 h) x (h.mem_cycles x)

/-- The identification of a minimal algebra with its cohomology carries `m₂` to the cohomology
product. -/
theorem cohomologyEquiv_m_two (h : 𝒜.IsMinimal) (x y : A) :
    h.cohomologyEquiv (𝒜.m 2 ![x, y]) = h.cohomologyEquiv x * h.cohomologyEquiv y := by
  simp only [cohomologyEquiv_apply, cohomology_mul_eq_cohomologyMul,
    cohomologyMul_cohomologyClass]

/-- The identification of a minimal algebra with its cohomology preserves degrees. -/
theorem isHomogeneous_cohomologyEquiv (h : 𝒜.IsMinimal) :
    LinearMap.IsHomogeneous h.cohomologyEquiv.toLinearMap 𝒜.grading.piece
      𝒜.cohomologyGrading.piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro p x hx
  rw [add_zero, LinearEquiv.coe_coe, cohomologyEquiv_apply]
  exact 𝒜.cohomologyClass_mem_cohomologyGrading_piece _ hx

end IsMinimal

end AInfinityAlgebra

/-- The `A∞` algebra of a nonunital DG algebra is minimal exactly when the differential
vanishes. -/
theorem IsNonUnitalDGAlgebra.isMinimal_toAInfinityAlgebra_iff {A : Type uA} [NonUnitalRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] {𝒜 : ℤ → Submodule R A}
    [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜] {d : A →ₗ[R] A}
    (h : IsNonUnitalDGAlgebra 𝒜 d) : h.toAInfinityAlgebra.IsMinimal ↔ d = 0 := by
  rw [AInfinityAlgebra.isMinimal_def, toAInfinityAlgebra_differential]

namespace AInfinityAlgebra

/-- The cohomology `A∞` algebra is minimal. -/
theorem isMinimal_cohomologyAInfinityAlgebra (𝒜 : AInfinityAlgebra R A) :
    𝒜.cohomologyAInfinityAlgebra.IsMinimal :=
  (isMinimal_iff_m_one_eq_zero _).2 fun _ ↦ 𝒜.cohomologyAInfinityAlgebra_m_one_apply _

end AInfinityAlgebra

namespace AInfinityHom

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

/-- Between minimal algebras, the map induced on cohomology is the linear part, transported along
the identifications of the algebras with their cohomology. -/
theorem cohomologyMap_cohomologyEquiv (hA : AA.IsMinimal) (hB : BB.IsMinimal)
    (f : AInfinityHom AA BB) (x : A) :
    f.cohomologyMap (hA.cohomologyEquiv x) = hB.cohomologyEquiv (f.linearPart x) := by
  simp only [AInfinityAlgebra.IsMinimal.cohomologyEquiv_apply, cohomologyMap_cohomologyClass]

/-- An `A∞` morphism between minimal algebras is a quasi-isomorphism exactly when its linear part
is bijective. -/
theorem isQuasiIso_iff_linearPart_bijective (hA : AA.IsMinimal) (hB : BB.IsMinimal)
    (f : AInfinityHom AA BB) :
    f.IsQuasiIso ↔ Function.Bijective f.linearPart := by
  have hcomm : ⇑f.cohomologyMap ∘ ⇑hA.cohomologyEquiv = ⇑hB.cohomologyEquiv ∘ ⇑f.linearPart :=
    funext (cohomologyMap_cohomologyEquiv hA hB f)
  rw [isQuasiIso_def, ← EquivLike.bijective_comp hA.cohomologyEquiv, hcomm,
    EquivLike.comp_bijective]

/-- Between minimal algebras, an `A∞` morphism is a quasi-isomorphism exactly when it is an
isomorphism of `A∞` algebras.  This upgrades a given quasi-isomorphism between minimal models to
an `A∞` isomorphism; it does not by itself provide the quasi-isomorphism needed for uniqueness. -/
theorem isQuasiIso_iff_isIso (hA : AA.IsMinimal) (hB : BB.IsMinimal) (f : AInfinityHom AA BB) :
    f.IsQuasiIso ↔ f.IsIso := by
  rw [isQuasiIso_iff_linearPart_bijective hA hB, isIso_iff_linearPart_bijective]

/-- A quasi-isomorphism between minimal algebras is an isomorphism of `A∞` algebras. -/
theorem IsQuasiIso.isIso (hA : AA.IsMinimal) (hB : BB.IsMinimal) {f : AInfinityHom AA BB}
    (hf : f.IsQuasiIso) : f.IsIso :=
  (isQuasiIso_iff_isIso hA hB f).1 hf

/-- Between minimal algebras, the linear part of an `A∞` morphism carries `m₂` to `m₂`: the
defect of multiplicativity is a boundary, and a minimal algebra has no nonzero boundaries. -/
theorem linearPart_m_two (hA : AA.IsMinimal) (hB : BB.IsMinimal) (f : AInfinityHom AA BB)
    (a b : A) : f.linearPart (AA.m 2 ![a, b]) = BB.m 2 ![f.linearPart a, f.linearPart b] := by
  have hab := f.linearPart_m_two_sub_mem_boundaries (hA.mem_cycles a) (hA.mem_cycles b)
  rwa [(AInfinityAlgebra.isMinimal_iff_boundaries_eq_bot BB).1 hB, Submodule.mem_bot,
    sub_eq_zero] at hab

end AInfinityHom

namespace AInfinityStrictHom

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

/-- Between minimal algebras without operations above arity two, a degree-preserving linear map
which carries `m₂` to `m₂` is a strict morphism. -/
def ofMapMTwo (hA : AA.IsMinimal) (hB : BB.IsMinimal) (hmA : ∀ n, 3 ≤ n → AA.m n = 0)
    (hmB : ∀ n, 3 ≤ n → BB.m n = 0) (f : A →ₗ[R] B)
    (hf : LinearMap.IsHomogeneous f AA.grading.piece BB.grading.piece 0)
    (hf₂ : ∀ a b, f (AA.m 2 ![a, b]) = BB.m 2 ![f a, f b]) : AInfinityStrictHom AA BB where
  toLinearMap := f
  map_mem' ha := by simpa only [add_zero] using hf.map_mem ha
  map_m' n := by
    ext x
    rw [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply]
    match n with
    | 0 => simp
    | 1 => simp [hA.m_one, hB.m_one]
    | 2 =>
      obtain ⟨a, b, rfl⟩ : ∃ a b, x = ![a, b] :=
        ⟨x 0, x 1, funext fun i ↦ by fin_cases i <;> rfl⟩
      rw [hf₂]
      congr 1
      funext i
      fin_cases i <;> rfl
    | n + 3 => simp [hmA (n + 3) (by omega), hmB (n + 3) (by omega)]

/-- The strict morphism `ofMapMTwo` has the given underlying map. -/
@[simp]
theorem coe_ofMapMTwo (hA : AA.IsMinimal) (hB : BB.IsMinimal) (hmA : ∀ n, 3 ≤ n → AA.m n = 0)
    (hmB : ∀ n, 3 ≤ n → BB.m n = 0) (f : A →ₗ[R] B)
    (hf : LinearMap.IsHomogeneous f AA.grading.piece BB.grading.piece 0)
    (hf₂ : ∀ a b, f (AA.m 2 ![a, b]) = BB.m 2 ![f a, f b]) :
    ⇑(ofMapMTwo hA hB hmA hmB f hf hf₂) = f := (rfl)

end AInfinityStrictHom

end TauCeti
