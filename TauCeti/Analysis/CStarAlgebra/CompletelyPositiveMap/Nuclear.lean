/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Order
import TauCeti.Analysis.CStarAlgebra.Basic
import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Matrix
import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Pi

/-!
# Nuclear completely positive maps and nuclear C⋆-algebras

A completely positive map `φ : A → B` between C⋆-algebras is a *nuclear contraction* when it is a
point-norm limit of composites `A → M_n → B` of completely positive contractions through full
matrix algebras `M_n = CStarMatrix (Fin n) (Fin n) ℂ`. In the finite-set form
(`CompletelyPositiveMap.IsNuclearContraction`): for every finite set `F ⊆ A` and `ε > 0` there
are completely positive contractions `α : A → M_n` and `β : M_n → B` with `‖β (α a) - φ a‖ < ε`
for `a ∈ F`. Equivalently, there is a net of such factorizations converging to `φ` pointwise
(`CompletelyPositiveMap.IsNuclearContraction.of_tendsto`,
`CompletelyPositiveMap.IsNuclearContraction.exists_tendsto`). A nuclear contraction is a
contraction (`CompletelyPositiveMap.IsNuclearContraction.norm_apply_le`).

A general completely positive map is *nuclear* (`CompletelyPositiveMap.IsNuclear`) when it is a
nonnegative multiple of a nuclear contraction, and a C⋆-algebra `A` is *nuclear*
(`TauCeti.CStarAlgebra.IsNuclear`) when its identity map is a nuclear contraction. This is the
completely positive approximation property; it is a different notion from nuclear operators
between Banach spaces, and from the approximation property of a Banach space.

## Main declarations

* `CompletelyPositiveMap.IsNuclearContraction`: the finite-set form of nuclearity.
* `CompletelyPositiveMap.IsNuclear`: nonnegative multiples of nuclear contractions.
* `TauCeti.CStarAlgebra.IsNuclear`: the identity of `A` is a nuclear contraction.

## Main statements

* `CompletelyPositiveMap.isNuclearContraction_zero`: the zero map is a nuclear contraction,
  through `M_0`.
* `CompletelyPositiveMap.IsNuclearContraction.comp_left` and
  `CompletelyPositiveMap.IsNuclearContraction.comp_right`: composing a nuclear contraction on either
  side with a completely positive contraction gives a nuclear contraction.
* `CompletelyPositiveMap.IsNuclear.comp_left` and `CompletelyPositiveMap.IsNuclear.comp_right`:
  composing a nuclear map on either side with any completely positive map gives a nuclear map.
* `CompletelyPositiveMap.IsNuclearContraction.of_forall_exists`: point-norm closedness; a point-norm
  limit of nuclear contractions is a nuclear contraction.
* `CompletelyPositiveMap.IsNuclearContraction.smul`: multiples `c • φ` with `c ≤ 1` of nuclear
  contractions are nuclear contractions.
* `TauCeti.CStarAlgebra.IsNuclear.of_retract`: a retract of a nuclear C⋆-algebra through
  completely positive contractions is nuclear.
* `TauCeti.CStarAlgebra.IsNuclear.of_starAlgEquiv`: nuclearity is invariant under star
  isomorphism, and the matrix algebras `M_n(ℂ)` (`TauCeti.CStarAlgebra.isNuclear_cstarMatrix`),
  `M_n(M_m(ℂ))` (`TauCeti.CStarAlgebra.isNuclear_cstarMatrix_cstarMatrix`) and `ℂ`
  (`TauCeti.CStarAlgebra.isNuclear_complex`) are nuclear.
* `TauCeti.CStarAlgebra.isNuclear_pi_cstarMatrix`: a finite direct sum `⊕_i M_{n_i}` of full
  matrix algebras is nuclear. It embeds unitally in `M_N`, `N = Σ n_i`, through
  `CompletelyPositiveMap.blockDiagonal`, and the compression to the diagonal blocks
  (`CompletelyPositiveMap.pi` of the `CompletelyPositiveMap.submatrix` maps) is a completely
  positive contraction back, so the identity factors exactly through one matrix algebra.

## References

* B. Blackadar, *Operator Algebras: Theory of C⋆-Algebras and von Neumann Algebras*,
  Encyclopaedia of Mathematical Sciences 122, Springer (2006), IV.3.1.4.
-/

public section

open scoped CStarAlgebra ComplexOrder NNReal Topology

open Filter

namespace CompletelyPositiveMap

variable {A B C D : Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

/-- A completely positive map `φ : A → B` is a **nuclear contraction** when it is a point-norm
limit of composites `A → M_n → B` of completely positive contractions through full matrix
algebras: for every finite set `F ⊆ A` and `ε > 0` there are completely positive contractions
`α : A → M_n` and `β : M_n → B` with `‖β (α a) - φ a‖ < ε` for `a ∈ F`. -/
def IsNuclearContraction (φ : A →CP B) : Prop :=
  ∀ (F : Finset A) (ε : ℝ), 0 < ε →
    ∃ (n : ℕ) (α : A →CP CStarMatrix (Fin n) (Fin n) ℂ)
      (β : CStarMatrix (Fin n) (Fin n) ℂ →CP B),
      (∀ a, ‖α a‖ ≤ ‖a‖) ∧ (∀ x, ‖β x‖ ≤ ‖x‖) ∧ ∀ a ∈ F, ‖β (α a) - φ a‖ < ε

/-- Unfolding `IsNuclearContraction`: the finite-set approximation property by composites
`A → M_n → B` of completely positive contractions. -/
theorem isNuclearContraction_iff {φ : A →CP B} :
    φ.IsNuclearContraction ↔ ∀ (F : Finset A) (ε : ℝ), 0 < ε →
      ∃ (n : ℕ) (α : A →CP CStarMatrix (Fin n) (Fin n) ℂ)
        (β : CStarMatrix (Fin n) (Fin n) ℂ →CP B),
        (∀ a, ‖α a‖ ≤ ‖a‖) ∧ (∀ x, ‖β x‖ ≤ ‖x‖) ∧ ∀ a ∈ F, ‖β (α a) - φ a‖ < ε :=
  Iff.rfl

/-- A nuclear contraction is a contraction. -/
theorem IsNuclearContraction.norm_apply_le {φ : A →CP B} (h : φ.IsNuclearContraction) (a : A) :
    ‖φ a‖ ≤ ‖a‖ := by
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨n, α, β, hα, hβ, hF⟩ := h {a} ε hε
  calc ‖φ a‖ ≤ ‖β (α a)‖ + ‖β (α a) - φ a‖ := norm_le_norm_add_norm_sub (β (α a)) (φ a)
    _ < ‖a‖ + ε := add_lt_add_of_le_of_lt ((hβ _).trans (hα a)) (hF a (Finset.mem_singleton_self a))

/-- The zero map is a nuclear contraction, through the zero matrix algebra `M_0`. -/
theorem isNuclearContraction_zero : (0 : A →CP B).IsNuclearContraction :=
  fun _ _ hε ↦ ⟨0, 0, 0, fun a ↦ by simp, fun x ↦ by simp, fun a _ ↦ by simpa using hε⟩

/-- **Point-norm closedness.** If `φ` is a point-norm limit of nuclear contractions, then `φ` is a
nuclear contraction. -/
theorem IsNuclearContraction.of_forall_exists {φ : A →CP B}
    (h : ∀ (F : Finset A) (ε : ℝ), 0 < ε →
      ∃ ψ : A →CP B, ψ.IsNuclearContraction ∧ ∀ a ∈ F, ‖ψ a - φ a‖ < ε) :
    φ.IsNuclearContraction := by
  intro F ε hε
  obtain ⟨ψ, hψ, hψF⟩ := h F (ε / 2) (half_pos hε)
  obtain ⟨n, α, β, hα, hβ, hF⟩ := hψ F (ε / 2) (half_pos hε)
  refine ⟨n, α, β, hα, hβ, fun a ha ↦ ?_⟩
  calc ‖β (α a) - φ a‖ ≤ ‖β (α a) - ψ a‖ + ‖ψ a - φ a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hF a ha) (hψF a ha)
    _ = ε := add_halves ε

/-- **Net form, converse direction.** A pointwise limit of composites `A → M_{n i} → B` of
completely positive contractions along a nontrivial filter is a nuclear contraction. -/
theorem IsNuclearContraction.of_tendsto {φ : A →CP B} {ι : Type*} {l : Filter ι} [l.NeBot]
    {n : ι → ℕ} (α : ∀ i, A →CP CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)
    (β : ∀ i, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ →CP B) (hα : ∀ i a, ‖α i a‖ ≤ ‖a‖)
    (hβ : ∀ i x, ‖β i x‖ ≤ ‖x‖) (h : ∀ a, Tendsto (fun i ↦ β i (α i a)) l (𝓝 (φ a))) :
    φ.IsNuclearContraction := by
  intro F ε hε
  have hev : ∀ᶠ i in l, ∀ a ∈ F, ‖β i (α i a) - φ a‖ < ε :=
    (eventually_all_finset F).2 fun a _ ↦ by
      simpa [dist_eq_norm] using (Metric.tendsto_nhds.1 (h a)) ε hε
  obtain ⟨i, hi⟩ := hev.exists
  exact ⟨n i, α i, β i, hα i, hβ i, hi⟩

/-- **Net form.** A nuclear contraction is the pointwise limit of a net of composites
`A → M_{n i} → B` of completely positive contractions, indexed by pairs of a finite set and a
natural number, directed by `atTop`. -/
theorem IsNuclearContraction.exists_tendsto {φ : A →CP B} (h : φ.IsNuclearContraction) :
    ∃ (n : Finset A × ℕ → ℕ) (α : ∀ i, A →CP CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)
      (β : ∀ i, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ →CP B),
      (∀ i a, ‖α i a‖ ≤ ‖a‖) ∧ (∀ i x, ‖β i x‖ ≤ ‖x‖) ∧
        ∀ a, Tendsto (fun i ↦ β i (α i a)) atTop (𝓝 (φ a)) := by
  classical
  choose n α β hα hβ hF using fun i : Finset A × ℕ ↦ h i.1 (1 / (i.2 + 1)) Nat.one_div_pos_of_nat
  refine ⟨n, α, β, hα, hβ, fun a ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_⟩
  obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
  refine eventually_atTop.2 ⟨({a}, K), fun i hi ↦ ?_⟩
  rw [dist_eq_norm]
  refine (hF i a (hi.1 (Finset.mem_singleton_self a))).trans_le (le_trans ?_ hK.le)
  gcongr
  exact_mod_cast hi.2

/-- Composing a nuclear contraction with a completely positive contraction on the left gives a
nuclear contraction. -/
theorem IsNuclearContraction.comp_left {φ : A →CP B} (h : φ.IsNuclearContraction) (ψ : B →CP C)
    (hψ : ∀ b, ‖ψ b‖ ≤ ‖b‖) : (ψ.comp φ).IsNuclearContraction := by
  intro F ε hε
  obtain ⟨n, α, β, hα, hβ, hF⟩ := h F ε hε
  refine ⟨n, α, ψ.comp β, hα, fun x ↦ ?_, fun a ha ↦ ?_⟩
  · rw [comp_apply]
    exact (hψ _).trans (hβ x)
  · have : (ψ.comp β) (α a) - (ψ.comp φ) a = ψ (β (α a) - φ a) := by
      rw [comp_apply, comp_apply, map_sub]
    rw [this]
    exact (hψ _).trans_lt (hF a ha)

/-- Composing a nuclear contraction with a completely positive contraction on the right gives a
nuclear contraction. -/
theorem IsNuclearContraction.comp_right {φ : A →CP B} (h : φ.IsNuclearContraction) (θ : D →CP A)
    (hθ : ∀ d, ‖θ d‖ ≤ ‖d‖) : (φ.comp θ).IsNuclearContraction := by
  classical
  intro F ε hε
  obtain ⟨n, α, β, hα, hβ, hF⟩ := h (F.image θ) ε hε
  refine ⟨n, α.comp θ, β, fun d ↦ ?_, hβ, fun d hd ↦ ?_⟩
  · rw [comp_apply]
    exact (hα _).trans (hθ d)
  · rw [comp_apply, comp_apply]
    exact hF (θ d) (Finset.mem_image_of_mem θ hd)

/-- **Scaling down.** A multiple `c • φ` with `c ≤ 1` of a nuclear contraction is a nuclear
contraction. -/
theorem IsNuclearContraction.smul {φ : A →CP B} (h : φ.IsNuclearContraction) {c : ℝ≥0}
    (hc : c ≤ 1) : (c • φ).IsNuclearContraction := by
  intro F ε hε
  obtain ⟨n, α, β, hα, hβ, hF⟩ := h F ε hε
  have hcn (b : B) : ‖c • b‖ ≤ ‖b‖ := by
    rw [NNReal.smul_def, norm_smul_of_nonneg c.coe_nonneg]
    exact mul_le_of_le_one_left (norm_nonneg b) hc
  refine ⟨n, α, c • β, hα, fun x ↦ (hcn _).trans (hβ x), fun a ha ↦ ?_⟩
  rw [smul_apply, smul_apply, ← smul_sub]
  exact (hcn _).trans_lt (hF a ha)

/-- A completely positive map is **nuclear** when it is a nonnegative multiple `c • ψ` of a nuclear
contraction `ψ`. -/
def IsNuclear (φ : A →CP B) : Prop :=
  ∃ (c : ℝ≥0) (ψ : A →CP B), ψ.IsNuclearContraction ∧ φ = c • ψ

/-- Unfolding `IsNuclear`: `φ` is a nonnegative multiple of a nuclear contraction. -/
theorem isNuclear_iff {φ : A →CP B} :
    φ.IsNuclear ↔ ∃ (c : ℝ≥0) (ψ : A →CP B), ψ.IsNuclearContraction ∧ φ = c • ψ :=
  Iff.rfl

/-- A nuclear contraction is nuclear. -/
theorem IsNuclearContraction.isNuclear {φ : A →CP B} (h : φ.IsNuclearContraction) :
    φ.IsNuclear :=
  ⟨1, φ, h, (one_smul _ _).symm⟩

/-- Nonnegative multiples of nuclear maps are nuclear. -/
theorem IsNuclear.smul {φ : A →CP B} (h : φ.IsNuclear) (c : ℝ≥0) : (c • φ).IsNuclear := by
  obtain ⟨d, ψ, hψ, rfl⟩ := h
  exact ⟨c * d, ψ, hψ, (mul_smul c d ψ).symm⟩

/-- Composing a nuclear map with a completely positive map on the left gives a nuclear map. -/
theorem IsNuclear.comp_left {φ : A →CP B} (h : φ.IsNuclear) (ψ : B →CP C) :
    (ψ.comp φ).IsNuclear := by
  obtain ⟨c, θ, hθ, rfl⟩ := h
  obtain ⟨K, ψ', hψ', rfl⟩ := exists_norm_apply_le_and_eq_smul ψ
  refine ⟨K * c, ψ'.comp θ, hθ.comp_left ψ' hψ', ?_⟩
  rw [smul_comp, comp_smul, mul_smul]

/-- Composing a nuclear map with a completely positive map on the right gives a nuclear map. -/
theorem IsNuclear.comp_right {φ : A →CP B} (h : φ.IsNuclear) (θ : D →CP A) :
    (φ.comp θ).IsNuclear := by
  obtain ⟨c, ψ, hψ, rfl⟩ := h
  obtain ⟨K, θ', hθ', rfl⟩ := exists_norm_apply_le_and_eq_smul θ
  refine ⟨c * K, ψ.comp θ', hψ.comp_right θ' hθ', ?_⟩
  rw [smul_comp, comp_smul, mul_smul]

end CompletelyPositiveMap

namespace TauCeti.CStarAlgebra

open CompletelyPositiveMap

variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A C⋆-algebra is **nuclear** when its identity map is a nuclear contraction: the identity is a
point-norm limit of composites `A → M_n → A` of completely positive contractions. -/
class IsNuclear : Prop where
  /-- The identity map is a nuclear contraction. -/
  isNuclearContraction_id : (CompletelyPositiveMap.id A).IsNuclearContraction

variable {A} {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A retract of a nuclear C⋆-algebra through completely positive contractions is nuclear: if
`ρ ∘ σ = id` for completely positive contractions `σ : A → B` and `ρ : B → A` with `B` nuclear,
then `A` is nuclear. -/
theorem IsNuclear.of_retract [IsNuclear B] (σ : A →CP B) (ρ : B →CP A)
    (hσ : ∀ a, ‖σ a‖ ≤ ‖a‖) (hρ : ∀ b, ‖ρ b‖ ≤ ‖b‖) (h : ∀ a, ρ (σ a) = a) : IsNuclear A := by
  refine ⟨?_⟩
  convert ((IsNuclear.isNuclearContraction_id (A := B)).comp_right σ hσ).comp_left ρ hρ using 1
  ext a
  simp [h]

/-- Nuclearity is invariant under star isomorphism. -/
theorem IsNuclear.of_starAlgEquiv (e : A ≃⋆ₐ[ℂ] B) [IsNuclear B] : IsNuclear A :=
  .of_retract (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap e)
    (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap e.symm)
    (NonUnitalStarAlgHom.norm_apply_le e) (NonUnitalStarAlgHom.norm_apply_le e.symm)
    (by simp)

/-- The full matrix algebra `M_n(ℂ)` is nuclear: the identity factors through itself. -/
private theorem isNuclear_cstarMatrix_fin (n : ℕ) : IsNuclear (CStarMatrix (Fin n) (Fin n) ℂ) :=
  ⟨fun _ _ hε ↦ ⟨n, .id _, .id _, fun x ↦ (congrArg norm (id_apply x)).le,
    fun x ↦ (congrArg norm (id_apply x)).le,
    fun _ _ ↦ by simpa using hε⟩⟩

/-- The full matrix algebra `M_m(ℂ)` over a finite index type is nuclear. -/
instance isNuclear_cstarMatrix (m : Type*) [Fintype m] :
    IsNuclear (CStarMatrix m m ℂ) :=
  have := isNuclear_cstarMatrix_fin (Fintype.card m)
  .of_starAlgEquiv (CStarMatrix.reindexₐ ℂ ℂ (Fintype.equivFin m))

/-- The matrix algebras `M_n(M_m(ℂ))` are nuclear, through `M_n(M_m(ℂ)) ≃ M_{n × m}(ℂ)`. -/
instance isNuclear_cstarMatrix_cstarMatrix (n m : Type*) [Fintype n] [Fintype m] :
    IsNuclear (CStarMatrix n n (CStarMatrix m m ℂ)) :=
  .of_starAlgEquiv (CStarMatrix.compStarAlgEquiv ℂ n m ℂ)

/-- The complex numbers form a nuclear C⋆-algebra, through `ℂ ≃ M_1(ℂ)`. -/
instance isNuclear_complex : IsNuclear ℂ :=
  .of_starAlgEquiv (CStarMatrix.toOneByOne (Fin 1) ℂ ℂ)

/-- **Finite direct sums of matrix algebras are nuclear.** The product `Π i, M_{n i}(ℂ)` embeds in
`M_{Σ i, n i}(ℂ)` block-diagonally, and the compression to the diagonal blocks is a completely
positive contraction back, so the identity factors exactly through one matrix algebra. -/
instance isNuclear_pi_cstarMatrix {ι : Type*} [Fintype ι] (n : ι → Type*) [∀ i, Fintype (n i)] :
    IsNuclear (∀ i, CStarMatrix (n i) (n i) ℂ) := by
  classical
  let σ : (∀ i, CStarMatrix (n i) (n i) ℂ) →CP CStarMatrix (Σ i, n i) (Σ i, n i) ℂ :=
    blockDiagonal fun i ↦ CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
      (Pi.evalStarAlgHom ℂ (fun i ↦ CStarMatrix (n i) (n i) ℂ) i)
  let ρ : CStarMatrix (Σ i, n i) (Σ i, n i) ℂ →CP ∀ i, CStarMatrix (n i) (n i) ℂ :=
    pi fun i ↦ submatrix (Sigma.mk i)
  have hσ1 : σ 1 = 1 := blockDiagonal_map_one _ fun i ↦ by simp
  have hσ : ∀ a, ‖σ a‖ ≤ ‖a‖ :=
    (CompletelyPositiveMapClass.norm_map_one_le_one_iff σ).1 (hσ1 ▸ CStarRing.norm_one_le)
  have hρ (x : CStarMatrix (Σ i, n i) (Σ i, n i) ℂ) : ‖ρ x‖ ≤ ‖x‖ := by
    refine norm_pi_apply_le (fun i ↦ (CompletelyPositiveMapClass.norm_map_one_le_one_iff _).1 ?_) x
    rw [submatrix_map_one sigma_mk_injective]
    exact CStarRing.norm_one_le
  refine .of_retract σ ρ hσ hρ fun a ↦ ?_
  ext i j k
  simp [σ, ρ]

end TauCeti.CStarAlgebra
