/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.ZariskiClosure

/-!
# Neurovarieties and algebraic coefficient images

A coefficient parametrization `c : W → (σ → K)` sends parameters to coordinates in a specified
coordinate space `K^σ`; its realized image is the coefficient image `Set.range c`. The
`neurovariety` of `c` is the Zariski closure of this image, with equations over `K` and points
in `K^σ`, and `IsAlgebraicImage c` says that the image is already Zariski closed. These are
kept separate: a polynomial parametrization need not have a Zariski closed image, so the
neurovariety is defined for every parametrization without assuming closedness.

The parametrization lands in its neurovariety (`toNeurovariety`); its image there is exactly
the coefficient image, so it is surjective onto the neurovariety exactly when the image is
algebraic. Corestriction to the coefficient image itself is Mathlib's `Set.rangeFactorization`,
which is always surjective. Over finitely many coordinates, the neurovariety and the closedness
of the image do not depend on the choice of linear coordinates. More generally, two faithful
linear presentations `E₁ (c₁ w) = F w = E₂ (c₂ w)` of the same map in finitely many coordinates
have coefficient maps related by a linear map which restricts to a bijection between their
neurovarieties, and their coefficient images are algebraic simultaneously
(`exists_linearMap_comp_eq_bijOn_neurovariety`,
`isAlgebraicImage_iff_isAlgebraicImage_of_injective`).
Zero-padding the coordinates, as when the degree bound of a polynomial coefficient presentation
is raised, transports the neurovariety along the padding, preserves and reflects algebraicity of
the image, and the padding coordinates vanish on the neurovariety.

The closure convention follows Finkel–Rodriguez–Wu–Yahl, *Activation degree thresholds and
expressiveness of polynomial neural networks*,
[arXiv:2408.04569v4](https://arxiv.org/abs/2408.04569v4), §1.1, equations (3)–(4), where the
neurovariety is the Zariski closure of the neuromanifold. Shahverdi, *Algebraic Complexity and
Neurovariety of Linear Convolutional Networks*,
[arXiv:2401.16613v1](https://arxiv.org/abs/2401.16613v1), §2.2, instead uses the word for a
neuromanifold that is already closed; that situation is `IsAlgebraicImage` here.
-/

public section

namespace TauCeti.Neuromanifold

open MvPolynomial

variable {W σ τ K : Type*} [Field K]

/-- The neurovariety of a coefficient parametrization `c : W → (σ → K)`: the Zariski closure,
for equations over `K`, of its coefficient image. -/
def neurovariety (c : W → σ → K) : Set (σ → K) := zariskiClosure K (Set.range c)

/-- The neurovariety is the Zariski closure of the coefficient image. -/
theorem neurovariety_def (c : W → σ → K) :
    neurovariety c = zariskiClosure K (Set.range c) := (rfl)

/-- A point lies in the neurovariety exactly when it satisfies every polynomial equation over
`K` satisfied by all parametrized coefficient vectors. -/
theorem mem_neurovariety_iff {c : W → σ → K} {z : σ → K} :
    z ∈ neurovariety c ↔
      ∀ p : MvPolynomial σ K, (∀ w, eval (c w) p = 0) → eval z p = 0 := by
  simp [neurovariety_def]

/-- The coefficient image lies in the neurovariety. -/
theorem range_subset_neurovariety (c : W → σ → K) : Set.range c ⊆ neurovariety c :=
  (zariskiClosure K).le_closure _

/-- Every parametrized coefficient vector lies in the neurovariety. -/
@[simp] theorem apply_mem_neurovariety (c : W → σ → K) (w : W) : c w ∈ neurovariety c :=
  range_subset_neurovariety c ⟨w, rfl⟩

/-- The neurovariety and the coefficient image satisfy the same polynomial equations. -/
@[simp] theorem vanishingIdeal_neurovariety (c : W → σ → K) :
    vanishingIdeal K (neurovariety c) = vanishingIdeal K (Set.range c) :=
  vanishingIdeal_zariskiClosure _

/-- The neurovariety is the smallest zero locus containing the coefficient image. -/
theorem neurovariety_subset_zeroLocus_iff {c : W → σ → K} {I : Ideal (MvPolynomial σ K)} :
    neurovariety c ⊆ zeroLocus K I ↔ Set.range c ⊆ zeroLocus K I :=
  zariskiClosure_le_zeroLocus_iff

/-- The coefficient image of `c` is algebraic when it coincides with the neurovariety, that is,
when it is Zariski closed. -/
def IsAlgebraicImage (c : W → σ → K) : Prop := neurovariety c = Set.range c

/-- The image is algebraic exactly when the neurovariety is the coefficient image. -/
theorem isAlgebraicImage_iff {c : W → σ → K} :
    IsAlgebraicImage c ↔ neurovariety c = Set.range c := Iff.rfl

/-- The image is algebraic exactly when the coefficient image is Zariski closed. -/
theorem isAlgebraicImage_iff_isClosed {c : W → σ → K} :
    IsAlgebraicImage c ↔ (zariskiClosure K).IsClosed (Set.range c) :=
  (zariskiClosure K).isClosed_iff.symm

/-- The image is algebraic exactly when the coefficient image is the zero locus of an ideal. -/
theorem isAlgebraicImage_iff_exists_zeroLocus {c : W → σ → K} :
    IsAlgebraicImage c ↔ ∃ I : Ideal (MvPolynomial σ K), zeroLocus K I = Set.range c :=
  isAlgebraicImage_iff_isClosed.trans zariskiClosure_isClosed_iff

/-- With no parameters the neurovariety is empty. -/
@[simp] theorem neurovariety_of_isEmpty [IsEmpty W] (c : W → σ → K) : neurovariety c = ∅ := by
  rw [neurovariety_def, Set.range_eq_empty, zariskiClosure_empty]

/-- With no parameters the (empty) coefficient image is algebraic. -/
theorem isAlgebraicImage_of_isEmpty [IsEmpty W] (c : W → σ → K) : IsAlgebraicImage c := by
  rw [isAlgebraicImage_iff, neurovariety_of_isEmpty, Set.range_eq_empty]

/-- A parametrization onto the whole coefficient space has the whole space as neurovariety. -/
theorem neurovariety_eq_univ_of_surjective {c : W → σ → K} (hc : Function.Surjective c) :
    neurovariety c = Set.univ := by
  rw [neurovariety_def, hc.range_eq, zariskiClosure_univ]

/-- A parametrization onto the whole coefficient space has algebraic image. -/
theorem isAlgebraicImage_of_surjective {c : W → σ → K} (hc : Function.Surjective c) :
    IsAlgebraicImage c := by
  rw [isAlgebraicImage_iff, neurovariety_eq_univ_of_surjective hc, hc.range_eq]

/-- The parametrization `c`, regarded as a map into its neurovariety. -/
def toNeurovariety (c : W → σ → K) : W → neurovariety c :=
  Set.codRestrict c _ (apply_mem_neurovariety c)

/-- Forgetting membership in the neurovariety recovers the parametrization. -/
@[simp] theorem coe_toNeurovariety (c : W → σ → K) (w : W) :
    (toNeurovariety c w : σ → K) = c w := (rfl)

/-- The image of the parametrization in its neurovariety is exactly the coefficient image. -/
@[simp] theorem range_toNeurovariety (c : W → σ → K) :
    Set.range (toNeurovariety c) = Subtype.val ⁻¹' Set.range c :=
  Set.range_codRestrict _

/-- The parametrization is surjective onto its neurovariety exactly when its image is
algebraic. -/
theorem surjective_toNeurovariety_iff {c : W → σ → K} :
    Function.Surjective (toNeurovariety c) ↔ IsAlgebraicImage c :=
  (Set.surjective_codRestrict _).trans eq_comm

/-- Changing finitely many linear coordinates by an invertible `K`-linear map transports the
neurovariety along that map. -/
theorem neurovariety_linearEquiv_comp [Finite σ] (e : (σ → K) ≃ₗ[K] (τ → K))
    (c : W → σ → K) : neurovariety (e ∘ c) = e '' neurovariety c := by
  rw [neurovariety_def, neurovariety_def, Set.range_comp, zariskiClosure_image_linearEquiv]

/-- Whether the coefficient image is algebraic does not depend on the choice of finitely many
linear coordinates. -/
theorem isAlgebraicImage_linearEquiv_comp_iff [Finite σ]
    (e : (σ → K) ≃ₗ[K] (τ → K)) {c : W → σ → K} :
    IsAlgebraicImage (e ∘ c) ↔ IsAlgebraicImage c := by
  rw [isAlgebraicImage_iff_isClosed, isAlgebraicImage_iff_isClosed, Set.range_comp,
    zariskiClosure_isClosed_image_linearEquiv_iff]

/-- Let `f : K^σ → K^τ` and `g : K^τ → K^σ` be `K`-linear maps over finitely many coordinates
with `g (f (c w)) = c w` for every parameter `w`. Then `f` transports the neurovariety of `c` onto
the neurovariety of `f ∘ c`. -/
theorem neurovariety_linearMap_comp [Finite σ] [Finite τ] (f : (σ → K) →ₗ[K] (τ → K))
    (g : (τ → K) →ₗ[K] (σ → K)) {c : W → σ → K} (h : ∀ w, g (f (c w)) = c w) :
    neurovariety (f ∘ c) = f '' neurovariety c := by
  rw [neurovariety_def, neurovariety_def, Set.range_comp,
    zariskiClosure_image_linearMap_of_leftInvOn f g (by rintro _ ⟨w, rfl⟩; exact h w)]

/-- Let `f : K^σ → K^τ` and `g : K^τ → K^σ` be `K`-linear maps over finitely many coordinates
with `g (f (c w)) = c w` for every parameter `w`. Then `f ∘ c` has algebraic image exactly when
`c` does. -/
theorem isAlgebraicImage_linearMap_comp_iff [Finite σ] [Finite τ] (f : (σ → K) →ₗ[K] (τ → K))
    (g : (τ → K) →ₗ[K] (σ → K)) {c : W → σ → K} (h : ∀ w, g (f (c w)) = c w) :
    IsAlgebraicImage (f ∘ c) ↔ IsAlgebraicImage c := by
  rw [isAlgebraicImage_iff_isClosed, isAlgebraicImage_iff_isClosed, Set.range_comp,
    zariskiClosure_isClosed_image_linearMap_iff_of_leftInvOn f g (by rintro _ ⟨w, rfl⟩; exact h w)]

/-! ### Independence of the faithful linear presentation

A map `F : W → M` into a `K`-vector space, such as the realization map of a model with
`M = X → Y`, may be presented by coefficient maps `c₁ : W → K^σ` and `c₂ : W → K^τ` with injective
linear evaluations `E₁` and `E₂`, so that `E₁ (c₁ w) = F w = E₂ (c₂ w)`. Then each coefficient map
is a linear function of the other, and the two neurovarieties and the algebraicity of the two
coefficient images agree. -/

section Presentation

variable {M : Type*} [AddCommGroup M] [Module K M] {F : W → M}
  {E₁ : (σ → K) →ₗ[K] M} {E₂ : (τ → K) →ₗ[K] M} {c₁ : W → σ → K} {c₂ : W → τ → K}

/-- Two faithful linear presentations of the same map `F` in finitely many coordinates are
related by a linear map which sends the first coefficient map to the second and restricts to a
bijection between their neurovarieties. -/
theorem exists_linearMap_comp_eq_bijOn_neurovariety [Finite σ] [Finite τ]
    (hE₁ : Function.Injective E₁) (hE₂ : Function.Injective E₂)
    (h₁ : ∀ w, E₁ (c₁ w) = F w) (h₂ : ∀ w, E₂ (c₂ w) = F w) :
    ∃ φ : (σ → K) →ₗ[K] (τ → K), φ ∘ c₁ = c₂ ∧
      Set.BijOn φ (neurovariety c₁) (neurovariety c₂) := by
  -- Composing each evaluation with a linear left inverse of the other compares the coefficients.
  obtain ⟨G₁, hG₁⟩ := E₁.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hE₁)
  obtain ⟨G₂, hG₂⟩ := E₂.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hE₂)
  have hφ (w : W) : (G₂ ∘ₗ E₁) (c₁ w) = c₂ w := by
    simpa [h₁, ← h₂] using LinearMap.congr_fun hG₂ (c₂ w)
  have hψ (w : W) : (G₁ ∘ₗ E₂) (c₂ w) = c₁ w := by
    simpa [h₂, ← h₁] using LinearMap.congr_fun hG₁ (c₁ w)
  have hψφ (w : W) : (G₁ ∘ₗ E₂) ((G₂ ∘ₗ E₁) (c₁ w)) = c₁ w := by rw [hφ, hψ]
  have hc : ⇑(G₂ ∘ₗ E₁) ∘ c₁ = c₂ := funext hφ
  refine ⟨G₂ ∘ₗ E₁, hc, ?_⟩
  rw [← hc, neurovariety_linearMap_comp _ _ hψφ]
  exact (leftInvOn_zariskiClosure _ _ (by rintro _ ⟨w, rfl⟩; exact hψφ w)).injOn.bijOn_image

/-- Whether the coefficient image is algebraic does not depend on the faithful linear
presentation in finitely many coordinates: two such presentations of the same map have algebraic
coefficient images simultaneously. -/
theorem isAlgebraicImage_iff_isAlgebraicImage_of_injective [Finite σ] [Finite τ]
    (hE₁ : Function.Injective E₁) (hE₂ : Function.Injective E₂)
    (h₁ : ∀ w, E₁ (c₁ w) = F w) (h₂ : ∀ w, E₂ (c₂ w) = F w) :
    IsAlgebraicImage c₁ ↔ IsAlgebraicImage c₂ := by
  obtain ⟨φ, hφ, hbij⟩ := exists_linearMap_comp_eq_bijOn_neurovariety hE₁ hE₂ h₁ h₂
  obtain ⟨ψ, hψ, hbij'⟩ := exists_linearMap_comp_eq_bijOn_neurovariety hE₂ hE₁ h₂ h₁
  constructor
  · intro h
    rw [isAlgebraicImage_iff, ← hbij.image_eq, h, ← Set.range_comp, hφ]
  · intro h
    rw [isAlgebraicImage_iff, ← hbij'.image_eq, h, ← Set.range_comp, hψ]

end Presentation

/-! ### Zero-padding the coordinates

Raising the degree bound of a polynomial coefficient presentation embeds the old coordinates into
the new ones and pads the extra coordinates with zero. This is extension by zero along an
injective map of coordinate types `s : σ → τ`. -/

section ExtendByZero

variable {s : σ → τ}

/-- Zero-padding the coordinates along an injective `s` transports the neurovariety along the
padding. No finiteness of the coordinates is needed. -/
theorem neurovariety_extendByZero_comp (hs : Function.Injective s) (c : W → σ → K) :
    neurovariety (Function.ExtendByZero.linearMap K K s ∘ c) =
      Function.ExtendByZero.linearMap K K s '' neurovariety c := by
  rw [neurovariety_def, neurovariety_def, Set.range_comp, zariskiClosure_image_extendByZero hs]

/-- Whether the coefficient image is algebraic does not change under zero-padding the coordinates
along an injective `s`. -/
theorem isAlgebraicImage_extendByZero_comp_iff (hs : Function.Injective s) {c : W → σ → K} :
    IsAlgebraicImage (Function.ExtendByZero.linearMap K K s ∘ c) ↔ IsAlgebraicImage c := by
  rw [isAlgebraicImage_iff_isClosed, isAlgebraicImage_iff_isClosed, Set.range_comp,
    zariskiClosure_isClosed_image_extendByZero_iff hs]

/-- The padding coordinates vanish on the neurovariety of a zero-padded parametrization. -/
theorem apply_eq_zero_of_mem_neurovariety_extendByZero_comp (s : σ → τ) {c : W → σ → K}
    {z : τ → K} (hz : z ∈ neurovariety (Function.ExtendByZero.linearMap K K s ∘ c)) {t : τ}
    (ht : t ∉ Set.range s) : z t = 0 := by
  rw [neurovariety_def, Set.range_comp] at hz
  exact apply_eq_zero_of_mem_zariskiClosure_image_extendByZero s hz ht

end ExtendByZero

end TauCeti.Neuromanifold
