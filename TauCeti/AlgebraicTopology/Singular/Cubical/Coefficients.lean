/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Normalized

/-!
# Change of coefficients for cubical chains

A ring homomorphism `φ : R →+* S` applies coefficientwise to unnormalized cubical chains, giving a
`φ`-semilinear map `TauCeti.CubicalChain.mapRingHom` that preserves degenerate chains and commutes
with boundaries, continuous push-forwards, and dimension casts. Passing to quotients modulo
degenerate chains yields the induced `φ`-semilinear map `TauCeti.NormalizedCubicalChain.mapRingHom`
on normalized cubical chains, and a ring isomorphism `e : R ≃+* S` induces a semilinear equivalence
`TauCeti.NormalizedCubicalChain.ringEquiv` in any universe of spaces and rings.

Because `TauCeti.NormalizedCubicalChain X R n` decouples the universe of the space `X` from the
universe of the coefficient ring `R`, applying `NormalizedCubicalChain.ringEquiv` to
`ULift.ringEquiv : ULift.{u} R ≃+* R` relates normalized cubical chains of `X : Type u` over
`ULift.{u} R` (the carrier of `TauCeti.normalizedCubicalChainComplex (ULift.{u} R)`) to normalized
cubical chains of `X` over `R`.

## Main definitions

* `TauCeti.CubicalChain.mapRingHom`: change of coefficients on unnormalized cubical chains along a
  semiring homomorphism.
* `TauCeti.CubicalChain.ringEquiv`: semilinear equivalence of unnormalized cubical chains induced by
  a semiring isomorphism.
* `TauCeti.NormalizedCubicalChain.mapRingHom`: change of coefficients on normalized cubical chains
  along a ring homomorphism.
* `TauCeti.NormalizedCubicalChain.ringEquiv`: semilinear equivalence of normalized cubical chains
  induced by a ring isomorphism.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II.
-/

public section

noncomputable section

open Finsupp

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace CubicalChain

section Semiring

variable {R S T : Type*} [Semiring R] [Semiring S] [Semiring T]

variable (X) in
/-- Change of coefficients on unnormalized cubical chains along a semiring homomorphism
`φ : R →+* S`. -/
def mapRingHom (φ : R →+* S) (n : ℕ) :
    CubicalChain X R n →ₛₗ[φ] CubicalChain X S n :=
  Finsupp.mapRange.linearMap φ.toSemilinearMap

@[simp]
theorem mapRingHom_apply (φ : R →+* S) {n : ℕ} (g : CubicalChain X R n) (c : SingularCube X n) :
    mapRingHom X φ n g c = φ (g c) := by
  simp [mapRingHom]

@[simp]
theorem mapRingHom_single (φ : R →+* S) {n : ℕ} (c : SingularCube X n) (a : R) :
    mapRingHom X φ n (single c a) = single c (φ a) := by
  simp [mapRingHom]

@[simp]
theorem mapRingHom_id (n : ℕ) :
    mapRingHom X (RingHom.id R) n = LinearMap.id :=
  Finsupp.mapRange.linearMap_id

theorem mapRingHom_comp {φ : R →+* S} {ψ : S →+* T} {χ : R →+* T} [RingHomCompTriple φ ψ χ]
    (n : ℕ) :
    mapRingHom X χ n = (mapRingHom X ψ n).comp (mapRingHom X φ n) := by
  ext c
  simp [← RingHomCompTriple.comp_apply (σ₁₂ := φ) (σ₂₃ := ψ) (σ₁₃ := χ)]

/-- Change of coefficients commutes with push-forward along a continuous map. -/
theorem mapRingHom_map (φ : R →+* S) (f : C(X, Y)) {n : ℕ} (g : CubicalChain X R n) :
    mapRingHom Y φ n (map R f n g) = map S f n (mapRingHom X φ n g) := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single c r => simp

/-- Change of coefficients commutes with dimension reindexing. -/
theorem mapRingHom_cast (φ : R →+* S) {n m : ℕ} (h : n = m) (g : CubicalChain X R n) :
    mapRingHom X φ m (cast R h g) = cast S h (mapRingHom X φ n g) := by
  subst h
  simp

/-- Change of coefficients preserves degenerate unnormalized chains. -/
theorem mapRingHom_mem_degenerate (φ : R →+* S) {n : ℕ} {g : CubicalChain X R n}
    (hg : g ∈ degenerate X R n) : mapRingHom X φ n g ∈ degenerate X S n := by
  rw [mem_degenerate_iff] at hg ⊢
  intro c hc
  rw [mapRingHom_apply, hg c hc, map_zero]

/-- An injective semiring homomorphism reflects degenerate unnormalized chains. -/
theorem mapRingHom_mem_degenerate_iff (φ : R →+* S) (hφ : Function.Injective φ) {n : ℕ}
    (g : CubicalChain X R n) :
    mapRingHom X φ n g ∈ degenerate X S n ↔ g ∈ degenerate X R n := by
  refine ⟨fun hg ↦ ?_, mapRingHom_mem_degenerate φ⟩
  rw [mem_degenerate_iff] at hg ⊢
  intro c hc
  exact hφ (by rw [← mapRingHom_apply, hg c hc, map_zero])

variable (X) in
/-- Semilinear equivalence of unnormalized cubical chains induced by a semiring isomorphism. -/
def ringEquiv (e : R ≃+* S) (n : ℕ) :
    haveI := RingHomInvPair.of_ringEquiv e
    haveI := RingHomInvPair.symm (↑e : R →+* S) (e.symm : S →+* R)
    CubicalChain X R n ≃ₛₗ[(↑e : R →+* S)] CubicalChain X S n :=
  haveI := RingHomInvPair.of_ringEquiv e
  haveI := RingHomInvPair.symm (↑e : R →+* S) (e.symm : S →+* R)
  Finsupp.mapRange.linearEquiv e.toSemilinearEquiv

@[simp]
theorem ringEquiv_apply (e : R ≃+* S) {n : ℕ} (g : CubicalChain X R n) :
    ringEquiv X e n g = mapRingHom X (↑e : R →+* S) n g :=
  (rfl)

@[simp]
theorem ringEquiv_symm_apply (e : R ≃+* S) {n : ℕ} (g : CubicalChain X S n) :
    haveI := RingHomInvPair.of_ringEquiv e
    haveI := RingHomInvPair.symm (↑e : R →+* S) (e.symm : S →+* R)
    (ringEquiv X e n).symm g = mapRingHom X (e.symm : S →+* R) n g :=
  (rfl)

end Semiring

section Ring

variable {R S : Type*} [Ring R] [Ring S]

/-- Change of coefficients commutes with the cubical boundary operator. -/
theorem mapRingHom_boundary (φ : R →+* S) {n : ℕ} (g : CubicalChain X R (n + 1)) :
    mapRingHom X φ n (boundary X R n g) = boundary X S n (mapRingHom X φ (n + 1) g) := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single c r =>
    simp only [boundary_single, mapRingHom_single, map_sum, map_smulₛₗ, map_sub, map_pow,
      map_neg, map_one]

end Ring

end CubicalChain

namespace NormalizedCubicalChain

variable {R S T : Type*} [Ring R] [Ring S] [Ring T]

variable (X) in
/-- Change of coefficients on normalized cubical chains along a ring homomorphism `φ : R →+* S`. -/
def mapRingHom (φ : R →+* S) (n : ℕ) :
    NormalizedCubicalChain X R n →ₛₗ[φ] NormalizedCubicalChain X S n :=
  Submodule.mapQ _ _ (CubicalChain.mapRingHom X φ n)
    fun _ hg ↦ CubicalChain.mapRingHom_mem_degenerate φ hg

@[simp]
theorem mapRingHom_mk (φ : R →+* S) {n : ℕ} (g : CubicalChain X R n) :
    mapRingHom X φ n (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk (CubicalChain.mapRingHom X φ n g) :=
  Submodule.mapQ_apply _ _ _ g

@[simp]
theorem mapRingHom_ofCube (φ : R →+* S) {n : ℕ} (c : SingularCube X n) :
    mapRingHom X φ n (ofCube X R c) = ofCube X S c := by
  rw [ofCube_def, ofCube_def, mapRingHom_mk, CubicalChain.mapRingHom_single, map_one]

@[simp]
theorem mapRingHom_id (n : ℕ) :
    mapRingHom X (RingHom.id R) n = LinearMap.id := by
  unfold mapRingHom
  simp only [CubicalChain.mapRingHom_id, Submodule.mapQ_id]

theorem mapRingHom_comp {φ : R →+* S} {ψ : S →+* T} {χ : R →+* T} [RingHomCompTriple φ ψ χ]
    (n : ℕ) :
    mapRingHom X χ n = (mapRingHom X ψ n).comp (mapRingHom X φ n) := by
  refine LinearMap.ext fun g ↦ ?_
  induction g using Submodule.Quotient.induction_on with
  | H g =>
    rw [mapRingHom_mk, LinearMap.comp_apply, mapRingHom_mk, mapRingHom_mk,
      CubicalChain.mapRingHom_comp (φ := φ) (ψ := ψ) (χ := χ), LinearMap.comp_apply]

/-- Change of coefficients on normalized cubical chains commutes with the boundary operator. -/
theorem mapRingHom_boundary (φ : R →+* S) {n : ℕ} (g : NormalizedCubicalChain X R (n + 1)) :
    mapRingHom X φ n (boundary X R n g) = boundary X S n (mapRingHom X φ (n + 1) g) := by
  induction g using Submodule.Quotient.induction_on with
  | H g =>
    rw [boundary_mk, mapRingHom_mk, mapRingHom_mk, boundary_mk, CubicalChain.mapRingHom_boundary]

/-- Change of coefficients on normalized cubical chains commutes with continuous push-forwards. -/
theorem mapRingHom_map (φ : R →+* S) (f : C(X, Y)) {n : ℕ} (g : NormalizedCubicalChain X R n) :
    mapRingHom Y φ n (map R f n g) = map S f n (mapRingHom X φ n g) := by
  induction g using Submodule.Quotient.induction_on with
  | H g =>
    rw [map_mk, mapRingHom_mk, mapRingHom_mk, map_mk, CubicalChain.mapRingHom_map]

/-- Change of coefficients on normalized cubical chains commutes with dimension reindexing. -/
theorem mapRingHom_cast (φ : R →+* S) {n m : ℕ} (h : n = m) (g : NormalizedCubicalChain X R n) :
    mapRingHom X φ m (cast R h g) = cast S h (mapRingHom X φ n g) := by
  subst h
  simp

/-- Change of coefficients carries the `R`-span of a set of cubes into its `S`-span. -/
theorem mapRingHom_mem_span_ofCube (φ : R →+* S) {n : ℕ} {A : Set (SingularCube X n)}
    {g : NormalizedCubicalChain X R n} (hg : g ∈ Submodule.span R (ofCube X R '' A)) :
    mapRingHom X φ n g ∈ Submodule.span S (ofCube X S '' A) := by
  induction hg using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨c, hc, rfl⟩ := h
    rw [mapRingHom_ofCube]
    exact Submodule.subset_span ⟨c, hc, rfl⟩
  | zero => simp
  | add _ _ _ _ ha hb =>
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  | smul r _ _ ha =>
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ (φ r) ha

variable (X) in
/-- Semilinear equivalence of normalized cubical chains induced by a ring isomorphism
`e : R ≃+* S`. -/
def ringEquiv (e : R ≃+* S) (n : ℕ) :
    haveI := RingHomInvPair.of_ringEquiv e
    haveI := RingHomInvPair.symm (↑e : R →+* S) (e.symm : S →+* R)
    NormalizedCubicalChain X R n ≃ₛₗ[(↑e : R →+* S)] NormalizedCubicalChain X S n :=
  haveI := RingHomInvPair.of_ringEquiv e
  haveI := RingHomInvPair.symm (↑e : R →+* S) (e.symm : S →+* R)
  { mapRingHom X (↑e : R →+* S) n with
    invFun := mapRingHom X (e.symm : S →+* R) n
    left_inv g := by
      have h := LinearMap.congr_fun
        (mapRingHom_comp (X := X) (φ := (↑e : R →+* S)) (ψ := (e.symm : S →+* R))
          (χ := RingHom.id R) n) g
      rw [mapRingHom_id, LinearMap.id_apply, LinearMap.comp_apply] at h
      exact h.symm
    right_inv g := by
      have h := LinearMap.congr_fun
        (mapRingHom_comp (X := X) (φ := (e.symm : S →+* R)) (ψ := (↑e : R →+* S))
          (χ := RingHom.id S) n) g
      rw [mapRingHom_id, LinearMap.id_apply, LinearMap.comp_apply] at h
      exact h.symm }

@[simp]
theorem ringEquiv_apply (e : R ≃+* S) {n : ℕ} (g : NormalizedCubicalChain X R n) :
    ringEquiv X e n g = mapRingHom X (↑e : R →+* S) n g :=
  (rfl)

@[simp]
theorem ringEquiv_symm_apply (e : R ≃+* S) {n : ℕ} (g : NormalizedCubicalChain X S n) :
    haveI := RingHomInvPair.of_ringEquiv e
    haveI := RingHomInvPair.symm (↑e : R →+* S) (e.symm : S →+* R)
    (ringEquiv X e n).symm g = mapRingHom X (e.symm : S →+* R) n g :=
  (rfl)

theorem ringEquiv_ofCube (e : R ≃+* S) {n : ℕ} (c : SingularCube X n) :
    ringEquiv X e n (ofCube X R c) = ofCube X S c :=
  mapRingHom_ofCube (↑e : R →+* S) c

/-- `NormalizedCubicalChain.ringEquiv` commutes with the normalized boundary operator. -/
theorem ringEquiv_boundary (e : R ≃+* S) {n : ℕ} (g : NormalizedCubicalChain X R (n + 1)) :
    ringEquiv X e n (boundary X R n g) = boundary X S n (ringEquiv X e (n + 1) g) :=
  mapRingHom_boundary (↑e : R →+* S) g

end NormalizedCubicalChain

end TauCeti

end
