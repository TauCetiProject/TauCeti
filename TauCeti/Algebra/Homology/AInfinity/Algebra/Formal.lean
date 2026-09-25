/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.DG
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Cohomology

/-!
# Minimal and formal `A∞` algebras

An `A∞` algebra is *minimal* when its unary operation `m₁` vanishes.  Every element of a minimal
algebra is then a cycle and no nonzero element is a boundary, so the class map identifies the
algebra with its cohomology, carrying `m₂` to the cohomology product.  Consequently an `A∞`
morphism between minimal algebras is a quasi-isomorphism exactly when its linear part is
bijective.

The cohomology `H(A)` of an `A∞` algebra `A` is a graded nonunital algebra, hence an `A∞`
algebra with zero `m₁`, the cohomology product as `m₂`, and no higher operations; this is
`AInfinityAlgebra.cohomologyAInfinityAlgebra`.  The algebra `A` is *formal* when it admits an
`A∞` quasi-isomorphism to this `A∞` algebra.  Over a field every `A∞` quasi-isomorphism has an
`A∞` inverse up to homotopy, so there the direction of the quasi-isomorphism is immaterial.
Minimal models are exactly what distinguishes the two notions: the cohomology of a minimal algebra
is the algebra itself, but formality asks in addition that the higher operations can be removed up
to quasi-isomorphism.

Formality is reflected along quasi-isomorphisms: if `A ⟶ B` is a quasi-isomorphism and `B` is
formal, then so is `A`, because a quasi-isomorphism identifies the two cohomology algebras
compatibly with their gradings.  A minimal algebra whose operations above arity two vanish is
formal, since the class map is then a strict isomorphism onto its cohomology; in particular a
graded nonunital algebra with zero differential is formal.

## Main definitions

* `TauCeti.AInfinityAlgebra.IsMinimal`: the unary operation vanishes.
* `TauCeti.AInfinityAlgebra.IsMinimal.cohomologyEquiv`: the identification of a minimal algebra
  with its cohomology.
* `TauCeti.AInfinityAlgebra.cohomologyAInfinityAlgebra`: the cohomology as an `A∞` algebra whose
  only nonzero operation is `m₂`.
* `TauCeti.AInfinityAlgebra.IsFormal`: existence of an `A∞` quasi-isomorphism to
  `cohomologyAInfinityAlgebra`.

## Main results

* `TauCeti.AInfinityAlgebra.isMinimal_iff_cycles_eq_top` and
  `TauCeti.AInfinityAlgebra.isMinimal_iff_boundaries_eq_bot`: minimality in terms of cycles and
  boundaries.
* `TauCeti.AInfinityHom.isQuasiIso_iff_bijective_linearPart`: between minimal algebras, a
  quasi-isomorphism is a morphism with bijective linear part.
* `TauCeti.AInfinityAlgebra.isMinimal_cohomologyAInfinityAlgebra`: the cohomology algebra is
  minimal.
* `TauCeti.AInfinityAlgebra.IsMinimal.isFormal`: a minimal algebra with vanishing higher operations
  is formal, and `TauCeti.IsNonUnitalDGAlgebra.isFormal_toAInfinityAlgebra_zero` specializes this to
  graded algebras with zero differential.
* `TauCeti.AInfinityAlgebra.IsFormal.of_isQuasiIso`: formality is reflected along
  quasi-isomorphisms.

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
theorem isMinimal_iff (𝒜 : AInfinityAlgebra R A) :
    𝒜.IsMinimal ↔ ∀ x : A, 𝒜.m 1 ![x] = 0 := by
  simp only [isMinimal_def, LinearMap.ext_iff, differential_apply, LinearMap.zero_apply]

/-- An `A∞` algebra is minimal exactly when every element is a cycle. -/
theorem isMinimal_iff_cycles_eq_top (𝒜 : AInfinityAlgebra R A) :
    𝒜.IsMinimal ↔ 𝒜.cycles = ⊤ := by
  rw [isMinimal_iff, Submodule.eq_top_iff']
  simp only [mem_cycles]

/-- An `A∞` algebra is minimal exactly when zero is its only boundary. -/
theorem isMinimal_iff_boundaries_eq_bot (𝒜 : AInfinityAlgebra R A) :
    𝒜.IsMinimal ↔ 𝒜.boundaries = ⊥ := by
  rw [isMinimal_iff, Submodule.eq_bot_iff]
  simp only [mem_boundaries, forall_exists_index, forall_apply_eq_imp_iff]

namespace IsMinimal

variable {𝒜 : AInfinityAlgebra R A}

/-- The unary operation of a minimal `A∞` algebra vanishes. -/
theorem m_one (h : 𝒜.IsMinimal) (x : Fin 1 → A) : 𝒜.m 1 x = 0 := by
  obtain ⟨y, rfl⟩ : ∃ y, x = ![y] := ⟨x 0, funext fun i ↦ by fin_cases i; rfl⟩
  exact (isMinimal_iff 𝒜).1 h y

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
  (LinearEquiv.ofTop 𝒜.cycles ((isMinimal_iff_cycles_eq_top 𝒜).1 h)).symm ≪≫ₗ
    (Submodule.quotEquivOfEqBot _ h.boundariesInCycles_eq_bot).symm

/-- The identification of a minimal algebra with its cohomology sends an element to its class. -/
@[simp]
theorem cohomologyEquiv_apply (h : 𝒜.IsMinimal) (x : A) :
    h.cohomologyEquiv x = 𝒜.cohomologyClass (h.mem_cycles x) := by
  rw [cohomologyEquiv, LinearEquiv.trans_apply, LinearEquiv.ofTop_symm_apply,
    Submodule.quotEquivOfEqBot_symm_apply, cohomologyClass_eq_mk]

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
theorem isQuasiIso_iff_bijective_linearPart (hA : AA.IsMinimal) (hB : BB.IsMinimal)
    (f : AInfinityHom AA BB) :
    f.IsQuasiIso ↔ Function.Bijective f.linearPart := by
  have hcomm : ⇑f.cohomologyMap ∘ ⇑hA.cohomologyEquiv = ⇑hB.cohomologyEquiv ∘ ⇑f.linearPart :=
    funext (cohomologyMap_cohomologyEquiv hA hB f)
  rw [isQuasiIso_iff, ← EquivLike.bijective_comp hA.cohomologyEquiv, hcomm,
    EquivLike.comp_bijective]

end AInfinityHom

namespace AInfinityAlgebra

/-! ### The cohomology as a formal `A∞` algebra -/

/-- The cohomology of an `A∞` algebra, as the `A∞` algebra of a graded nonunital algebra with zero
differential: `m₁ = 0`, `m₂` is the cohomology product, and all higher operations vanish. -/
noncomputable def cohomologyAInfinityAlgebra (𝒜 : AInfinityAlgebra R A) :
    AInfinityAlgebra R 𝒜.Cohomology :=
  (isNonUnitalDGAlgebra_zero 𝒜.cohomologyGrading.piece).toAInfinityAlgebra

/-- The grading of the cohomology `A∞` algebra is the grading of the cohomology. -/
@[simp]
theorem cohomologyAInfinityAlgebra_grading (𝒜 : AInfinityAlgebra R A) :
    𝒜.cohomologyAInfinityAlgebra.grading = 𝒜.cohomologyGrading := by
  rw [cohomologyAInfinityAlgebra, IsNonUnitalDGAlgebra.toAInfinityAlgebra_grading]
  exact InternalGrading.ext fun _ ↦ by rw [InternalGrading.ofDecomposition_piece]

/-- The unary operation of the cohomology `A∞` algebra vanishes. -/
@[simp]
theorem cohomologyAInfinityAlgebra_m_one_apply (𝒜 : AInfinityAlgebra R A)
    (x : Fin 1 → 𝒜.Cohomology) : 𝒜.cohomologyAInfinityAlgebra.m 1 x = 0 := by
  rw [cohomologyAInfinityAlgebra, IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_one_apply,
    LinearMap.zero_apply]

/-- The binary operation of the cohomology `A∞` algebra is the cohomology product. -/
@[simp]
theorem cohomologyAInfinityAlgebra_m_two_apply (𝒜 : AInfinityAlgebra R A)
    (x : Fin 2 → 𝒜.Cohomology) : 𝒜.cohomologyAInfinityAlgebra.m 2 x = x 0 * x 1 := by
  rw [cohomologyAInfinityAlgebra, IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_two_apply]

/-- The operations of arity at least three of the cohomology `A∞` algebra vanish. -/
theorem cohomologyAInfinityAlgebra_m_of_three_le (𝒜 : AInfinityAlgebra R A) {n : ℕ}
    (hn : 3 ≤ n) : 𝒜.cohomologyAInfinityAlgebra.m n = 0 := by
  rw [cohomologyAInfinityAlgebra, IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_of_three_le _ hn]

/-- The simp-normal form of `cohomologyAInfinityAlgebra_m_of_three_le`. -/
@[simp]
theorem cohomologyAInfinityAlgebra_m_add_three (𝒜 : AInfinityAlgebra R A) (n : ℕ) :
    𝒜.cohomologyAInfinityAlgebra.m (n + 3) = 0 :=
  𝒜.cohomologyAInfinityAlgebra_m_of_three_le (by omega)

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
  (IsNonUnitalDGAlgebra.isMinimal_toAInfinityAlgebra_iff _).2 rfl

/-! ### Formality -/

/-- An `A∞` algebra is **formal** when it admits an `A∞` quasi-isomorphism to its cohomology,
regarded as an `A∞` algebra whose only nonzero operation is the cohomology product `m₂`. -/
def IsFormal (𝒜 : AInfinityAlgebra R A) : Prop :=
  ∃ f : AInfinityHom 𝒜 𝒜.cohomologyAInfinityAlgebra, f.IsQuasiIso

/-- An `A∞` algebra is formal exactly when it has a quasi-isomorphism to its cohomology `A∞`
algebra. -/
theorem isFormal_iff (𝒜 : AInfinityAlgebra R A) :
    𝒜.IsFormal ↔ ∃ f : AInfinityHom 𝒜 𝒜.cohomologyAInfinityAlgebra, f.IsQuasiIso := Iff.rfl

variable {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B}

/-- A degree-preserving morphism between cohomology algebras is a strict morphism between the
corresponding cohomology `A∞` algebras. -/
private noncomputable def cohomologyStrictHom (φ : 𝒜.Cohomology →ₙₐ[R] ℬ.Cohomology)
    (hφ : ∀ {p : ℤ} {c : 𝒜.Cohomology}, c ∈ 𝒜.cohomologyGrading.piece p →
      φ c ∈ ℬ.cohomologyGrading.piece p) :
    AInfinityStrictHom 𝒜.cohomologyAInfinityAlgebra ℬ.cohomologyAInfinityAlgebra :=
  NonUnitalDGAlgHom.toAInfinityStrictHom
    (hA := isNonUnitalDGAlgebra_zero 𝒜.cohomologyGrading.piece)
    (hB := isNonUnitalDGAlgebra_zero ℬ.cohomologyGrading.piece)
    { toNonUnitalAlgHom := φ
      map_mem' := hφ
      map_d' := fun _ ↦ by simp only [LinearMap.zero_apply, map_zero] }

private theorem coe_cohomologyStrictHom (φ : 𝒜.Cohomology →ₙₐ[R] ℬ.Cohomology) (hφ) :
    ⇑(cohomologyStrictHom φ hφ) = φ :=
  NonUnitalDGAlgHom.coe_toAInfinityStrictHom _

/-- The map induced on cohomology by a quasi-isomorphism, as a linear equivalence. -/
private noncomputable def cohomologyLinearEquiv {f : AInfinityHom 𝒜 ℬ} (hf : f.IsQuasiIso) :
    𝒜.Cohomology ≃ₗ[R] ℬ.Cohomology :=
  LinearEquiv.ofBijective (f.cohomologyMap : 𝒜.Cohomology →ₗ[R] ℬ.Cohomology)
    ((AInfinityHom.isQuasiIso_iff f).1 hf)

private theorem cohomologyLinearEquiv_apply {f : AInfinityHom 𝒜 ℬ} (hf : f.IsQuasiIso)
    (c : 𝒜.Cohomology) : cohomologyLinearEquiv hf c = f.cohomologyMap c := (rfl)

/-- The inverse of the map induced on cohomology by a quasi-isomorphism, as a morphism of
cohomology algebras. -/
private noncomputable def cohomologyMapInv {f : AInfinityHom 𝒜 ℬ} (hf : f.IsQuasiIso) :
    ℬ.Cohomology →ₙₐ[R] 𝒜.Cohomology where
  toFun := (cohomologyLinearEquiv hf).symm
  map_smul' := (cohomologyLinearEquiv hf).symm.map_smul
  map_zero' := (cohomologyLinearEquiv hf).symm.map_zero
  map_add' := (cohomologyLinearEquiv hf).symm.map_add
  map_mul' x y := (cohomologyLinearEquiv hf).injective (by
    rw [LinearEquiv.apply_symm_apply, cohomologyLinearEquiv_apply, map_mul,
      ← cohomologyLinearEquiv_apply hf, ← cohomologyLinearEquiv_apply hf,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])

private theorem cohomologyMapInv_apply {f : AInfinityHom 𝒜 ℬ} (hf : f.IsQuasiIso)
    (c : ℬ.Cohomology) : cohomologyMapInv hf c = (cohomologyLinearEquiv hf).symm c := by
  rw [cohomologyMapInv, NonUnitalAlgHom.coe_mk]

/-- The inverse of the map induced on cohomology by a quasi-isomorphism preserves degrees. -/
private theorem cohomologyMapInv_mem {f : AInfinityHom 𝒜 ℬ} (hf : f.IsQuasiIso) {p : ℤ}
    {c : ℬ.Cohomology} (hc : c ∈ ℬ.cohomologyGrading.piece p) :
    cohomologyMapInv hf c ∈ 𝒜.cohomologyGrading.piece p := by
  have he : LinearMap.IsHomogeneous (cohomologyLinearEquiv hf).toLinearMap
      𝒜.cohomologyGrading.piece ℬ.cohomologyGrading.piece 0 := by
    rw [LinearMap.isHomogeneous_def]
    intro q x hx
    rw [add_zero, LinearEquiv.coe_coe, cohomologyLinearEquiv_apply]
    exact f.cohomologyMap_mem_cohomologyGrading_piece hx
  simpa only [cohomologyMapInv_apply, add_zero, LinearEquiv.coe_coe] using
    he.linearEquiv_symm.map_mem hc

/-- A quasi-isomorphism `𝒜 ⟶ ℬ` identifies the cohomology `A∞` algebras; this is the strict
morphism in the backward direction, the inverse of the induced map on cohomology. -/
private noncomputable def cohomologyStrictHomInv {f : AInfinityHom 𝒜 ℬ} (hf : f.IsQuasiIso) :
    AInfinityStrictHom ℬ.cohomologyAInfinityAlgebra 𝒜.cohomologyAInfinityAlgebra :=
  cohomologyStrictHom (cohomologyMapInv hf) (cohomologyMapInv_mem hf)

private theorem cohomologyStrictHomInv_isQuasiIso {f : AInfinityHom 𝒜 ℬ} (hf : f.IsQuasiIso) :
    (cohomologyStrictHomInv hf).toAInfinityHom.IsQuasiIso := by
  rw [AInfinityHom.isQuasiIso_iff_bijective_linearPart ℬ.isMinimal_cohomologyAInfinityAlgebra
    𝒜.isMinimal_cohomologyAInfinityAlgebra, AInfinityStrictHom.linearPart_toAInfinityHom,
    AInfinityStrictHom.coe_toLinearMap, cohomologyStrictHomInv, coe_cohomologyStrictHom,
    funext (cohomologyMapInv_apply hf)]
  exact (cohomologyLinearEquiv hf).symm.bijective

/-- Formality is reflected along quasi-isomorphisms: if `𝒜 ⟶ ℬ` is a quasi-isomorphism and `ℬ` is
formal, then `𝒜` is formal. -/
theorem IsFormal.of_isQuasiIso {f : AInfinityHom 𝒜 ℬ} (hf : f.IsQuasiIso) (hℬ : ℬ.IsFormal) :
    𝒜.IsFormal := by
  obtain ⟨g, hg⟩ := hℬ
  exact ⟨(cohomologyStrictHomInv hf).toAInfinityHom.comp (g.comp f),
    (cohomologyStrictHomInv_isQuasiIso hf).comp (hg.comp hf)⟩

namespace IsMinimal

/-- The identification of a minimal algebra with vanishing higher operations with its cohomology,
as a strict morphism to the cohomology `A∞` algebra. -/
private noncomputable def toCohomology (h : 𝒜.IsMinimal) (hm : ∀ n, 3 ≤ n → 𝒜.m n = 0) :
    AInfinityStrictHom 𝒜 𝒜.cohomologyAInfinityAlgebra where
  toLinearMap := h.cohomologyEquiv.toLinearMap
  map_mem' hx := by
    simpa only [add_zero, cohomologyAInfinityAlgebra_grading] using
      h.isHomogeneous_cohomologyEquiv.map_mem hx
  map_m' n := by
    ext x
    rw [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply]
    match n with
    | 0 => simp
    | 1 => simp [h.m_one]
    | 2 =>
      rw [cohomologyAInfinityAlgebra_m_two_apply]
      obtain ⟨a, b, rfl⟩ : ∃ a b, x = ![a, b] :=
        ⟨x 0, x 1, funext fun i ↦ by fin_cases i <;> rfl⟩
      exact h.cohomologyEquiv_m_two a b
    | n + 3 => simp [hm (n + 3) (by omega)]

/-- A minimal `A∞` algebra whose operations of arity at least three vanish is formal: the
identification with its cohomology is a strict isomorphism. -/
theorem isFormal (h : 𝒜.IsMinimal) (hm : ∀ n, 3 ≤ n → 𝒜.m n = 0) : 𝒜.IsFormal := by
  refine ⟨(h.toCohomology hm).toAInfinityHom, ?_⟩
  rw [AInfinityHom.isQuasiIso_iff_bijective_linearPart h 𝒜.isMinimal_cohomologyAInfinityAlgebra,
    AInfinityStrictHom.linearPart_toAInfinityHom]
  exact h.cohomologyEquiv.bijective

end IsMinimal

end AInfinityAlgebra

/-- The `A∞` algebra of a graded nonunital algebra with zero differential is formal. -/
theorem IsNonUnitalDGAlgebra.isFormal_toAInfinityAlgebra_zero {A : Type uA} [NonUnitalRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] (𝒜 : ℤ → Submodule R A)
    [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜] :
    (isNonUnitalDGAlgebra_zero 𝒜 (R := R)).toAInfinityAlgebra.IsFormal :=
  ((isMinimal_toAInfinityAlgebra_iff _).2 rfl).isFormal fun _ hn ↦
    toAInfinityAlgebra_m_of_three_le _ hn

end TauCeti
