/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Congr
public import TauCeti.Geometry.Manifold.ConnectedSum.Sphere

import TauCeti.Geometry.Manifold.ContMDiff.Parametrization

/-!
# Connected-sum decompositions and prime manifolds

The connected sum `TauCeti.ConnectedSum e₁ e₂` of two manifolds is built from a choice of
coordinate balls `e₁` and `e₂`. A *decomposition* of a manifold `M` as a connected sum forgets
those choices: `TauCeti.IsConnectedSumOf I k M N₁ N₂` says that `M` is `C^k` diffeomorphic to the
connected sum of `N₁` and `N₂` along some pair of coordinate balls, open embeddings of the model
space which are `C^k` local diffeomorphisms. The relation is symmetric in the two summands
(`TauCeti.IsConnectedSumOf.symm`) and invariant under diffeomorphisms of `M` and of the summands
(`TauCeti.isConnectedSumOf_congr`), and every nonempty `n`-manifold is the connected sum of itself
with the sphere `Sⁿ` (`TauCeti.isConnectedSumOf_sphere`). No orientations are involved: for
connected oriented summands, a decomposition along arbitrary balls is an oriented connected sum
of the summands with suitable orientations, so the relation records every way of writing `M` as a
connected sum of `N₁` and `N₂`.

Since `M # Sⁿ ≃ M`, the sphere is the unit for the connected sum, and the *prime* manifolds are the
atoms. A smooth `n`-manifold `M` is **prime** (`TauCeti.IsPrimeManifold n M`) when it is not
diffeomorphic to `Sⁿ` and whenever `M` is a connected sum of two closed smooth `n`-manifolds, one
of them is diffeomorphic to `Sⁿ`. The sphere is excluded, as `1` is excluded from the prime numbers,
so that prime decompositions are unique on the nose rather than up to inserting spheres. The
summands are required to be closed, that is compact and Hausdorff, as in the classical definition.
This is necessary. Let `N₁` be `M` with one point `c` doubled, a non-Hausdorff manifold, and take
a ball of `N₁` centred at `c` and the identity ball of `N₂ = ℝⁿ`. The connected sum removes `c`
and glues the punctured `ℝⁿ` onto the punctured ball, so it is `N₁` without `c`, which is `M`
again. Neither summand is a sphere, so without the restriction no manifold would be prime. The
definition is meant for closed connected manifolds; a noncompact manifold is never a connected sum
of two closed ones, so it is prime in this sense, but this is not the notion of interest there.

A manifold is a connected sum of finitely many manifolds `P 0, …, P (k - 1)`
(`TauCeti.IsIteratedConnectedSum n P M`) when it is `Sⁿ` for `k = 0`, and otherwise a connected sum
of `P 0` with a closed manifold which is a connected sum of `P 1, …, P (k - 1)`. Because each
decomposition along the way forgets its balls, this records every choice of balls in the
right-nested connected sum `P 0 # (P 1 # (⋯ # P (k - 1)))`. A prime decomposition of `M` is
such a presentation with every `P i` prime; the Kneser–Milnor theorem says that closed connected
orientable `3`-manifolds have exactly one, up to order and diffeomorphism of the factors.

## Main definitions

* `TauCeti.IsConnectedSumOf I k M N₁ N₂`: the manifold `M` is a connected sum of `N₁` and `N₂`.
* `TauCeti.IsPrimeManifold n M`: the smooth `n`-manifold `M` is prime.
* `TauCeti.IsIteratedConnectedSum n P M`: the smooth `n`-manifold `M` is a connected sum of the
  finitely many manifolds `P i`.

## Main results

* `TauCeti.IsConnectedSumOf.symm`: the summands of a connected-sum decomposition can be exchanged.
* `TauCeti.IsConnectedSumOf.congr`, `TauCeti.isConnectedSumOf_congr`: decompositions are invariant
  under diffeomorphisms of the manifold and of the summands.
* `TauCeti.isConnectedSumOf_sphere`: every nonempty `n`-manifold `M` is a connected sum of `M` and
  `Sⁿ`.
* `TauCeti.not_isPrimeManifold_sphere`, `TauCeti.IsConnectedSumOf.not_isPrimeManifold`: the sphere,
  and a connected sum of two closed manifolds neither of which is a sphere, are not prime.
* `Diffeomorph.isPrimeManifold_iff`: being prime is invariant under diffeomorphism.
* `Diffeomorph.isIteratedConnectedSum_iff`: being a connected sum of a family is invariant under
  diffeomorphism.
* `TauCeti.isIteratedConnectedSum_one`: a nonempty manifold is the connected sum of the one-element
  family consisting of itself.

## References

* H. Kneser, *Geschlossene Flächen in dreidimensionalen Mannigfaltigkeiten*, Jahresber. Deutsch.
  Math.-Verein. 38 (1929), 248–260.
* J. Milnor, *A unique decomposition theorem for 3-manifolds*, Amer. J. Math. 84 (1962), 1–7.
* J. Hempel, *3-Manifolds*, Annals of Mathematics Studies 86, Princeton University Press (1976),
  Chapter 3 (prime manifolds and the connected sum).
* A. Kosinski, *Differential Manifolds*, Academic Press (1993), Chapter VI, Section 1.
-/

public section

noncomputable section

open Set Function Filter Topology Metric
open scoped Manifold ContDiff EuclideanSpace

universe u

namespace TauCeti

/-! ### Connected-sum decompositions -/

section Relation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (k : ℕ∞)

/-- The manifold `M` is a **connected sum** of `N₁` and `N₂`: for some coordinate balls
`e₁ : E → N₁` and `e₂ : E → N₂`, open embeddings of the model vector space which are `C^k` local
diffeomorphisms, the connected sum `TauCeti.ConnectedSum e₁ e₂` is `C^k` diffeomorphic to `M`. -/
def IsConnectedSumOf (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (N₁ : Type*) [TopologicalSpace N₁] [T1Space N₁] [ChartedSpace H N₁]
    (N₂ : Type*) [TopologicalSpace N₂] [T1Space N₂] [ChartedSpace H N₂] : Prop :=
  ∃ (e₁ : E → N₁) (e₂ : E → N₂) (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂),
    IsLocalDiffeomorph 𝓘(ℝ, E) I k e₁ ∧ IsLocalDiffeomorph 𝓘(ℝ, E) I k e₂ ∧
      letI := ConnectedSum.chartedSpace (H := H) h₁ h₂
      Nonempty (ConnectedSum e₁ e₂ ≃ₘ^k⟮I, I⟯ M)

variable {I k}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  {N₁ : Type*} [TopologicalSpace N₁] [T1Space N₁] [ChartedSpace H N₁]
  {N₂ : Type*} [TopologicalSpace N₂] [T1Space N₂] [ChartedSpace H N₂]
  {N₁' : Type*} [TopologicalSpace N₁'] [T1Space N₁'] [ChartedSpace H N₁']
  {N₂' : Type*} [TopologicalSpace N₂'] [T1Space N₂'] [ChartedSpace H N₂']

/-- A connected sum along explicit coordinate balls, identified with `M` by a diffeomorphism,
exhibits `M` as a connected sum. -/
theorem isConnectedSumOf_of_diffeomorph {e₁ : E → N₁} {e₂ : E → N₂} (h₁ : IsOpenEmbedding e₁)
    (h₂ : IsOpenEmbedding e₂) (d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) I k e₁)
    (d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) I k e₂)
    (φ : letI := ConnectedSum.chartedSpace (H := H) h₁ h₂
      ConnectedSum e₁ e₂ ≃ₘ^k⟮I, I⟯ M) :
    IsConnectedSumOf I k M N₁ N₂ :=
  ⟨e₁, e₂, h₁, h₂, d₁, d₂, ⟨φ⟩⟩

/-- A connected-sum decomposition of `M` is one of every manifold diffeomorphic to `M`. -/
theorem IsConnectedSumOf.trans_diffeomorph (h : IsConnectedSumOf I k M N₁ N₂)
    (φ : M ≃ₘ^k⟮I, I⟯ M') : IsConnectedSumOf I k M' N₁ N₂ := by
  obtain ⟨e₁, e₂, h₁, h₂, d₁, d₂, ⟨ψ⟩⟩ := h
  let := ConnectedSum.chartedSpace (H := H) h₁ h₂
  exact ⟨e₁, e₂, h₁, h₂, d₁, d₂, ⟨ψ.trans φ⟩⟩

/-- **The summands of a connected-sum decomposition can be exchanged.** -/
theorem IsConnectedSumOf.symm [IsManifold I k N₁] [IsManifold I k N₂]
    (h : IsConnectedSumOf I k M N₁ N₂) : IsConnectedSumOf I k M N₂ N₁ := by
  obtain ⟨e₁, e₂, h₁, h₂, d₁, d₂, ⟨φ⟩⟩ := h
  let := ConnectedSum.chartedSpace (H := H) h₁ h₂
  let := ConnectedSum.chartedSpace (H := H) h₂ h₁
  exact ⟨e₂, e₁, h₂, h₁, d₂, d₁, ⟨(ConnectedSum.commDiffeomorph h₂ h₁ d₂ d₁).trans φ⟩⟩

/-- Being a connected sum of `N₁` and `N₂` does not depend on the order of the summands. -/
theorem isConnectedSumOf_comm [IsManifold I k N₁] [IsManifold I k N₂] :
    IsConnectedSumOf I k M N₁ N₂ ↔ IsConnectedSumOf I k M N₂ N₁ :=
  ⟨IsConnectedSumOf.symm, IsConnectedSumOf.symm⟩

/-- A diffeomorphism of the first summand carries a decomposition to a decomposition: the ball
`e₁` of `N₁` is replaced by `ψ ∘ e₁`. -/
private theorem IsConnectedSumOf.diffeomorph_left [ProperSpace E] [T2Space N₂] [T2Space N₁']
    [IsManifold I k N₁] [IsManifold I k N₂] [IsManifold I k N₁']
    (h : IsConnectedSumOf I k M N₁ N₂) (ψ : N₁ ≃ₘ^k⟮I, I⟯ N₁') :
    IsConnectedSumOf I k M N₁' N₂ := by
  obtain ⟨e₁, e₂, h₁, h₂, d₁, d₂, ⟨φ⟩⟩ := h
  have h₁' : IsOpenEmbedding (ψ ∘ e₁) := ψ.toHomeomorph.isOpenEmbedding.comp h₁
  have d₁' : IsLocalDiffeomorph 𝓘(ℝ, E) I k (ψ ∘ e₁) := fun v ↦
    (d₁ v).comp (hg := ψ.isLocalDiffeomorph (e₁ v))
  let := ConnectedSum.chartedSpace (H := H) h₁ h₂
  let := ConnectedSum.chartedSpace (H := H) h₁' h₂
  obtain ⟨χ⟩ := ConnectedSum.nonempty_diffeomorph_of_eventuallyEq (e₁' := ψ ∘ e₁) (e₂' := e₂) ψ
    (Diffeomorph.refl I N₂ k) EventuallyEq.rfl (Eventually.of_forall fun _ ↦ rfl) h₁ h₂ h₁' h₂ d₁
    d₂ d₁' d₂
  exact ⟨ψ ∘ e₁, e₂, h₁', h₂, d₁', d₂, ⟨χ.symm.trans φ⟩⟩

/-- **Connected-sum decompositions are invariant under diffeomorphisms** of the manifold and of
the two summands. -/
theorem IsConnectedSumOf.congr [ProperSpace E] [T2Space N₂] [T2Space N₁']
    [T2Space N₂'] [IsManifold I k N₁] [IsManifold I k N₂] [IsManifold I k N₁']
    [IsManifold I k N₂'] (h : IsConnectedSumOf I k M N₁ N₂) (φ : M ≃ₘ^k⟮I, I⟯ M')
    (ψ₁ : N₁ ≃ₘ^k⟮I, I⟯ N₁') (ψ₂ : N₂ ≃ₘ^k⟮I, I⟯ N₂') : IsConnectedSumOf I k M' N₁' N₂' :=
  (((h.diffeomorph_left ψ₁).symm.diffeomorph_left ψ₂).symm).trans_diffeomorph φ

/-- Diffeomorphic manifolds have the same connected-sum decompositions into diffeomorphic
summands. -/
theorem isConnectedSumOf_congr [ProperSpace E] [T2Space N₁] [T2Space N₂] [T2Space N₁']
    [T2Space N₂'] [IsManifold I k N₁] [IsManifold I k N₂] [IsManifold I k N₁']
    [IsManifold I k N₂'] (φ : M ≃ₘ^k⟮I, I⟯ M') (ψ₁ : N₁ ≃ₘ^k⟮I, I⟯ N₁')
    (ψ₂ : N₂ ≃ₘ^k⟮I, I⟯ N₂') :
    IsConnectedSumOf I k M N₁ N₂ ↔ IsConnectedSumOf I k M' N₁' N₂' :=
  ⟨fun h ↦ h.congr φ ψ₁ ψ₂, fun h ↦ h.congr φ.symm ψ₁.symm ψ₂.symm⟩

end Relation

/-! ### The connected sum with a sphere -/

section Sphere

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [Fact (Module.finrank ℝ F = n + 1)] {k : ℕ∞}
  {M : Type*} [TopologicalSpace M] [T1Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) k M]

/-- **Every manifold is a connected sum with a sphere**: a nonempty `C^k` manifold `M` modelled on
`ℝⁿ` is a connected sum of `M` and the unit sphere `Sⁿ`. -/
theorem isConnectedSumOf_sphere [Nonempty M] :
    IsConnectedSumOf (𝓡 n) k M M (sphere (0 : F) 1) := by
  obtain ⟨e, -, he, de⟩ := exists_isOpenEmbedding_isLocalDiffeomorph
    (F := EuclideanSpace ℝ (Fin n)) (n := k) (Classical.arbitrary M)
  have : Nontrivial F := Module.nontrivial_of_finrank_eq_succ (R := ℝ) (n := n) Fact.out
  obtain ⟨v⟩ : Nonempty (sphere (0 : F) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  exact isConnectedSumOf_of_diffeomorph he (isOpenEmbedding_sphereBall v) de
    (isLocalDiffeomorph_sphereBall v k) (connectedSumSphereDiffeomorph he de v)

end Sphere

/-! ### Prime manifolds -/

section Prime

variable (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- A smooth `n`-manifold `M` is **prime** when it is not diffeomorphic to the sphere `Sⁿ`, and
whenever `M` is a connected sum of two closed smooth `n`-manifolds, one of the two is diffeomorphic
to `Sⁿ`. The summands range over closed manifolds, compact and Hausdorff, in the universe of `M`.
-/
def IsPrimeManifold : Prop :=
  IsEmpty (M ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ∧
    ∀ (N₁ N₂ : Type u) [TopologicalSpace N₁] [T2Space N₁] [CompactSpace N₁]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) N₁] [IsManifold (𝓡 n) ∞ N₁]
      [TopologicalSpace N₂] [T2Space N₂] [CompactSpace N₂]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) N₂] [IsManifold (𝓡 n) ∞ N₂],
      IsConnectedSumOf (𝓡 n) ⊤ M N₁ N₂ →
        Nonempty (N₁ ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ∨
          Nonempty (N₂ ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

variable {n M}

/-- A prime manifold is not diffeomorphic to the sphere. -/
theorem IsPrimeManifold.isEmpty_diffeomorph_sphere (h : IsPrimeManifold n M) :
    IsEmpty (M ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  h.1

/-- In a connected-sum decomposition of a prime manifold into two closed manifolds, one summand
is diffeomorphic to the sphere. -/
theorem IsPrimeManifold.nonempty_diffeomorph_sphere_or (h : IsPrimeManifold n M)
    {N₁ N₂ : Type u} [TopologicalSpace N₁] [T2Space N₁] [CompactSpace N₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N₁] [IsManifold (𝓡 n) ∞ N₁]
    [TopologicalSpace N₂] [T2Space N₂] [CompactSpace N₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N₂] [IsManifold (𝓡 n) ∞ N₂]
    (hM : IsConnectedSumOf (𝓡 n) ⊤ M N₁ N₂) :
    Nonempty (N₁ ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ∨
      Nonempty (N₂ ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  h.2 N₁ N₂ hM

/-- A connected sum of two closed manifolds, neither of which is diffeomorphic to the sphere, is
not prime. -/
theorem IsConnectedSumOf.not_isPrimeManifold
    {N₁ N₂ : Type u} [TopologicalSpace N₁] [T2Space N₁] [CompactSpace N₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N₁] [IsManifold (𝓡 n) ∞ N₁]
    [TopologicalSpace N₂] [T2Space N₂] [CompactSpace N₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N₂] [IsManifold (𝓡 n) ∞ N₂]
    (hM : IsConnectedSumOf (𝓡 n) ⊤ M N₁ N₂)
    (h₁ : IsEmpty (N₁ ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (h₂ : IsEmpty (N₂ ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    ¬IsPrimeManifold n M := fun h ↦
  (h.nonempty_diffeomorph_sphere_or hM).elim (fun ⟨φ⟩ ↦ h₁.false φ) fun ⟨φ⟩ ↦ h₂.false φ

variable (n) in
/-- **The sphere is not prime.** -/
theorem not_isPrimeManifold_sphere :
    ¬IsPrimeManifold n (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := fun h ↦
  h.isEmpty_diffeomorph_sphere.false (Diffeomorph.refl _ _ _)

end Prime

/-! ### Connected sums of finitely many manifolds -/

section Iterated

variable (n : ℕ)

/-- The smooth `n`-manifold `M` is a **connected sum of the finitely many manifolds**
`P 0, …, P (k - 1)`: for `k = 0` it is diffeomorphic to the sphere `Sⁿ`, the empty connected sum,
and for `k + 1` manifolds it is a connected sum (`TauCeti.IsConnectedSumOf`) of `P 0` and of a
closed smooth `n`-manifold which is a connected sum of `P 1, …, P k`. -/
def IsIteratedConnectedSum : {k : ℕ} → (P : Fin k → Type u) → [∀ i, TopologicalSpace (P i)] →
    [∀ i, T1Space (P i)] → [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (P i)] →
    (M : Type u) → [TopologicalSpace M] → [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] → Prop
  | 0, _, _, _, _, M, _, _ =>
    Nonempty (M ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  | k + 1, P, _, _, _, M, _, _ =>
    ∃ (N : Type u) (_ : TopologicalSpace N) (_ : T2Space N) (_ : CompactSpace N)
      (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) N) (_ : IsManifold (𝓡 n) ∞ N),
      IsIteratedConnectedSum (k := k) (fun i ↦ P i.succ) N ∧ IsConnectedSumOf (𝓡 n) ⊤ M (P 0) N

variable {n} {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M']

/-- A manifold is a connected sum of the empty family exactly when it is diffeomorphic to the
sphere. -/
@[simp]
theorem isIteratedConnectedSum_zero_iff (P : Fin 0 → Type u) [∀ i, TopologicalSpace (P i)]
    [∀ i, T1Space (P i)] [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (P i)] :
    IsIteratedConnectedSum n P M ↔
      Nonempty (M ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  Iff.rfl

/-- A manifold is a connected sum of `P 0, …, P k` exactly when it is a connected sum of `P 0` and
of a closed manifold which is a connected sum of `P 1, …, P k`. -/
theorem isIteratedConnectedSum_succ_iff {k : ℕ} (P : Fin (k + 1) → Type u)
    [∀ i, TopologicalSpace (P i)] [∀ i, T1Space (P i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (P i)] :
    IsIteratedConnectedSum n P M ↔
      ∃ (N : Type u) (_ : TopologicalSpace N) (_ : T2Space N) (_ : CompactSpace N)
        (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) N) (_ : IsManifold (𝓡 n) ∞ N),
        IsIteratedConnectedSum n (fun i ↦ P i.succ) N ∧ IsConnectedSumOf (𝓡 n) ⊤ M (P 0) N :=
  Iff.rfl

/-- A presentation of `M` as a connected sum of finitely many manifolds is one of every manifold
diffeomorphic to `M`. -/
theorem IsIteratedConnectedSum.trans_diffeomorph {k : ℕ} {P : Fin k → Type u}
    [∀ i, TopologicalSpace (P i)] [∀ i, T1Space (P i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (P i)] (h : IsIteratedConnectedSum n P M)
    (φ : M ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ M') : IsIteratedConnectedSum n P M' := by
  cases k with
  | zero =>
    obtain ⟨ψ⟩ := h
    exact ⟨φ.symm.trans ψ⟩
  | succ k =>
    obtain ⟨N, _, _, _, _, _, hN, hM⟩ := h
    exact ⟨N, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, hN, hM.trans_diffeomorph φ⟩

end Iterated

end TauCeti

namespace Diffeomorph

open TauCeti

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M']

/-- **Being prime is invariant under diffeomorphism.** -/
theorem isPrimeManifold_iff (φ : M ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ M') :
    IsPrimeManifold n M ↔ IsPrimeManifold n M' := by
  -- A diffeomorphism transports both the sphere condition and every decomposition.
  have key {X Y : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
      [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y]
      (φ : X ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ Y) (h : IsPrimeManifold n X) : IsPrimeManifold n Y :=
    ⟨⟨fun ψ ↦ h.1.false (φ.trans ψ)⟩, fun N₁ N₂ _ _ _ _ _ _ _ _ _ _ hY ↦
      h.2 N₁ N₂ (hY.trans_diffeomorph φ.symm)⟩
  exact ⟨key φ, key φ.symm⟩

/-- **Being a connected sum of a family is invariant under diffeomorphism.** -/
theorem isIteratedConnectedSum_iff (φ : M ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ M') {k : ℕ} {P : Fin k → Type u}
    [∀ i, TopologicalSpace (P i)] [∀ i, T1Space (P i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (P i)] :
    IsIteratedConnectedSum n P M ↔ IsIteratedConnectedSum n P M' :=
  ⟨(·.trans_diffeomorph φ), (·.trans_diffeomorph φ.symm)⟩

end Diffeomorph

namespace TauCeti

section Single

variable {n : ℕ} {M : Type} [TopologicalSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- **A manifold is the connected sum of itself alone**: a nonempty smooth `n`-manifold `M`
diffeomorphic to `P 0` is the connected sum of the one-element family `P`, as `M ≃ P 0 # Sⁿ`. -/
theorem isIteratedConnectedSum_one (P : Fin 1 → Type) [∀ i, TopologicalSpace (P i)]
    [∀ i, T1Space (P i)] [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (P i)]
    [∀ i, IsManifold (𝓡 n) ∞ (P i)] (φ : P 0 ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ M) :
    IsIteratedConnectedSum n P M := by
  have : Nonempty (P 0) := ⟨φ.symm (Classical.arbitrary M)⟩
  refine ⟨sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ⟨Diffeomorph.refl _ _ _⟩, ?_⟩
  exact (isConnectedSumOf_sphere (M := P 0)).trans_diffeomorph φ

end Single

end TauCeti
