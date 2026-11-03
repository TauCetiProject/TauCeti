/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Limits
public import TauCeti.CategoryTheory.Monoidal.Pivotal.FrobeniusSchur.Simple
public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.Basic
public import TauCeti.RepresentationTheory.FDRep.Basic
public import TauCeti.RepresentationTheory.FDRep.Pivotal
import Mathlib.LinearAlgebra.PID
import TauCeti.RepresentationTheory.Invariants

/-!
# Frobenius–Schur indicators in `FDRep k G`

We compute the Ng–Schauenburg Frobenius–Schur indicators of a finite-dimensional representation
`V : FDRep k G` equipped with the standard spherical structure (`FDRep.Pivotal`) when `G` is finite
and `|G|` is invertible in `k`: for every `n : ℕ+`,

`TauCeti.frobeniusSchurIndicator k V n = (Nat.card G : k)⁻¹ * ∑ g : G, V.character (g ^ (n : ℕ))`.

Specializing to `n = 2` shows that the categorical second Frobenius–Schur indicator agrees with the
representation-theoretic indicator `FDRep.frobeniusSchurIndicator V = |G|⁻¹ ∑ g, χ_V(g²)`.
Combining this identification with the categorical trichotomy in
`TauCeti.CategoryTheory.Monoidal.Pivotal.FrobeniusSchur.Simple` yields the self-duality criterion
`FDRep.frobeniusSchurIndicator V ≠ 0 ↔ Nonempty (V ≅ Vᘁ)` and the `{1, 0, -1}` trichotomy for any
simple `V : FDRep k G` over an algebraically closed field in which `|G|` is invertible (including
characteristic `2` when `|G|` is odd).

Note that invertibility of `|G|` in `k` is genuinely required to equate the categorical indicator
with the character average: for `G = C₂` and `k = 𝔽₂`, the trivial `1`-dimensional representation
has `dim_k Hom(𝟙_, V ⊗ V) = 1` and identity rotation, so its categorical indicator is `1`, whereas
`(Nat.card G : k)⁻¹` vanishes in `𝔽₂`.

## Main results

* `FDRep.trace_rightComp_tensorUnit`: when `|G|` is invertible in `k`, the trace of postcomposition
  with `φ : W ⟶ W` on `𝟙_ (FDRep k G) ⟶ W` equals `|G|⁻¹ ∑ g : G, tr_W(φ ∘ ρ(g))`.
* `TauCeti.frobeniusSchurIndicator_fdRep`: `ν_n(V) = (Nat.card G : k)⁻¹ * ∑ g : G,
  V.character (g ^ (n : ℕ))` for `[Invertible (Nat.card G : k)]` (and
  `TauCeti.frobeniusSchurIndicator_fdRep_of_charZero` without an explicit invertibility hypothesis
  in characteristic zero).
* `TauCeti.frobeniusSchurIndicator_fdRep_two`, `TauCeti.frobeniusSchurIndicator_fdRepOf_two`, and
  `TauCeti.frobeniusSchurIndicator_fdRep_ofShrink_two`: agreement of the categorical `n = 2`
  indicator with `FDRep.frobeniusSchurIndicator` and
  `TauCeti.Representation.frobeniusSchurIndicator`.
* `FDRep.frobeniusSchurIndicator_eq_one_or_eq_zero_or_eq_neg_one`,
  `FDRep.frobeniusSchurIndicator_ne_zero_iff`, and `FDRep.frobeniusSchurIndicator_eq_zero_iff`:
  categorical trichotomy and self-duality criterion for simple representations whenever `|G|` is
  invertible in an algebraically closed field `k`.

## References

* S.-H. Ng, P. Schauenburg, *Higher Frobenius–Schur indicators for pivotal categories*, in
  *Hopf algebras and generalizations*, Contemp. Math. **441** (2007), 63–90, §§4–5
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.7
-/

public section

open CategoryTheory MonoidalCategory TauCeti

universe u v w

namespace FDRep

section Trace

variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [Invertible (Nat.card G : k)]

/-- When `|G|` is invertible in `k`, the trace of postcomposition with `φ : W ⟶ W` on
`𝟙_ (FDRep k G) ⟶ W` equals the group average `|G|⁻¹ ∑ g : G, tr_W(φ ∘ ρ(g))`. -/
theorem trace_rightComp_tensorUnit {W : FDRep k G} (φ : W ⟶ W) :
    LinearMap.trace k (𝟙_ (FDRep k G) ⟶ W) (Linear.rightComp k (𝟙_ (FDRep k G)) φ) =
      (Nat.card G : k)⁻¹ * ∑ g : G, LinearMap.trace k W (φ.hom.hom.hom ∘ₗ W.ρ g) := by
  have : Invertible (Fintype.card G : k) :=
    invertibleOfNonzero (Fintype.card_eq_nat_card (α := G) ▸ Invertible.ne_zero (Nat.card G : k))
  let W' : Rep k G := (forget₂ (FDRep k G) (Rep k G)).obj W
  let U' : Rep k G := (forget₂ (FDRep k G) (Rep k G)).obj (𝟙_ (FDRep k G))
  let φ' : W' ⟶ W' := (forget₂ (FDRep k G) (Rep k G)).map φ
  let e₁ : (𝟙_ (FDRep k G) ⟶ W) ≃ₗ[k] (U' ⟶ W') :=
    (FDRep.forget₂HomLinearEquiv (𝟙_ (FDRep k G)) W).symm
  have he₁ : e₁.conj (Linear.rightComp k (𝟙_ (FDRep k G)) φ) = Linear.rightComp k U' φ' := by
    ext f : 1
    simp only [e₁, φ', LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
      Linear.rightComp_apply]
    rw [FDRep.forget₂HomLinearEquiv_symm_apply, Functor.map_comp,
      FDRep.forget₂_map_forget₂HomLinearEquiv]
  -- `forget₂ (FDRep k G) (Rep k G)` sends `𝟙_ (FDRep k G)` definitionally to `Rep.trivial k G k`.
  have htr₁ : LinearMap.trace k (U' ⟶ W') (Linear.rightComp k U' φ') =
      LinearMap.trace k (Rep.trivial k G k ⟶ W') (Linear.rightComp k (Rep.trivial k G k) φ') :=
    rfl
  let e₂ : (Rep.trivial k G k ⟶ W') ≃ₗ[k] W'.ρ.invariants := Rep.trivialHomEquivInvariants W'
  have hφ' : ∀ v ∈ W'.ρ.invariants, φ'.hom.toLinearMap v ∈ W'.ρ.invariants :=
    fun v hv ↦ (((Rep.invariantsFunctor k G).map φ').hom ⟨v, hv⟩).2
  have he₂ : e₂.conj (Linear.rightComp k (Rep.trivial k G k) φ') =
      φ'.hom.toLinearMap.restrict hφ' := by
    ext ⟨v, hv⟩
    simp only [e₂, LinearMap.restrict_apply, LinearEquiv.conj_apply_apply, Linear.rightComp_apply,
      Rep.coe_trivialHomEquivInvariants_apply, Rep.hom_comp,
      Representation.IntertwiningMap.comp_apply]
    rw [Rep.trivialHomEquivInvariants_symm_apply_hom, one_smul]
    rfl
  have hφ : ∀ v ∈ Representation.invariants W.ρ,
      φ.hom.hom.hom v ∈ Representation.invariants W.ρ := hφ'
  -- `forget₂ (FDRep k G) (Rep k G)` acts as the identity on underlying representations and maps.
  have htr₂ : LinearMap.trace k W'.ρ.invariants (φ'.hom.toLinearMap.restrict hφ') =
      LinearMap.trace k (Representation.invariants W.ρ) (φ.hom.hom.hom.restrict hφ) :=
    rfl
  have hmem : ∀ w : W,
      (φ.hom.hom.hom ∘ₗ Representation.averageMap W.ρ) w ∈ Representation.invariants W.ρ :=
    fun w ↦ hφ _ (Representation.averageMap_invariant W.ρ w)
  have hres : φ.hom.hom.hom.restrict hφ =
      (φ.hom.hom.hom ∘ₗ Representation.averageMap W.ρ).restrict (fun w _ ↦ hmem w) := by
    ext ⟨v, hv⟩
    simp only [LinearMap.restrict_apply, LinearMap.comp_apply,
      Representation.averageMap_id W.ρ v hv]
  have havg : φ.hom.hom.hom ∘ₗ Representation.averageMap W.ρ =
      (Nat.card G : k)⁻¹ • ∑ g : G, (φ.hom.hom.hom ∘ₗ W.ρ g) := by
    rw [Representation.averageMap_eq_invOf_card_smul_norm, Representation.norm,
      LinearMap.comp_smul, invOf_eq_inv, Fintype.card_eq_nat_card]
    ext w
    simp [LinearMap.sum_apply]
  rw [← LinearMap.trace_conj' _ e₁, he₁, htr₁, ← LinearMap.trace_conj' _ e₂, he₂, htr₂, hres,
    LinearMap.trace_restrict_eq_of_forall_mem (Representation.invariants W.ρ) _ hmem, havg,
    map_smul, map_sum, smul_eq_mul]

end Trace

end FDRep

namespace TauCeti

section Indicator

variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G]

/-- In `FDRep k G` with its standard spherical structure, the `n`-th Frobenius–Schur indicator of
`V` equals `(Nat.card G : k)⁻¹ * ∑ g : G, V.character (g ^ (n : ℕ))` whenever `|G|` is invertible
in `k`. -/
theorem frobeniusSchurIndicator_fdRep [Invertible (Nat.card G : k)] (V : FDRep k G) (n : ℕ+) :
    frobeniusSchurIndicator k V n = (Nat.card G : k)⁻¹ * ∑ g : G, V.character (g ^ (n : ℕ)) := by
  rw [frobeniusSchurIndicator_eq_trace_rightComp, FDRep.trace_rightComp_tensorUnit]
  refine congrArg ((Nat.card G : k)⁻¹ * ·) (Finset.sum_congr rfl fun g _ ↦ ?_)
  have htr := congrArg (fun ψ : 𝟙_ (FGModuleCat k) ⟶ 𝟙_ (FGModuleCat k) ↦ ψ.hom.hom 1)
    (Action.trace_ρ_comp_tensorPowShiftIso_hom V g n.natPred)
  simp only [FGModuleCat.trace_hom_hom_one, FGModuleCat.hom_hom_comp, FDRep.hom_hom_action_ρ,
    PNat.natPred_add_one] at htr
  exact htr

/-- In characteristic zero, `|G|` is automatically invertible in `k`, so the `n`-th categorical
Frobenius–Schur indicator of `V : FDRep k G` is `|G|⁻¹ ∑ g : G, V.character (g ^ (n : ℕ))`. -/
theorem frobeniusSchurIndicator_fdRep_of_charZero [CharZero k] (V : FDRep k G) (n : ℕ+) :
    frobeniusSchurIndicator k V n = (Nat.card G : k)⁻¹ * ∑ g : G, V.character (g ^ (n : ℕ)) := by
  have : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact frobeniusSchurIndicator_fdRep V n

end Indicator

section Two

variable {k : Type} {G : Type v} [Field k] [Group G] [Fintype G] [Invertible (Nat.card G : k)]

/-- The categorical second Frobenius–Schur indicator of `V : FDRep k G` agrees with the
character-average indicator `FDRep.frobeniusSchurIndicator V`. -/
theorem frobeniusSchurIndicator_fdRep_two (V : FDRep k G) :
    frobeniusSchurIndicator k V 2 = FDRep.frobeniusSchurIndicator V := by
  rw [frobeniusSchurIndicator_fdRep, FDRep.frobeniusSchurIndicator_def,
    Representation.frobeniusSchurIndicator_def]
  simp [FDRep.character_ρ]

/-- The categorical second Frobenius–Schur indicator of `FDRep.of ρ` agrees with
`TauCeti.Representation.frobeniusSchurIndicator ρ`. -/
theorem frobeniusSchurIndicator_fdRepOf_two {W : Type} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (ρ : Representation k G W) :
    frobeniusSchurIndicator k (FDRep.of ρ) 2 = Representation.frobeniusSchurIndicator ρ := by
  rw [frobeniusSchurIndicator_fdRep_two, FDRep.frobeniusSchurIndicator_def, FDRep.of_ρ']

/-- The categorical second Frobenius–Schur indicator of `FDRep.ofShrink ρ` agrees with
`TauCeti.Representation.frobeniusSchurIndicator ρ` for representations in any universe. -/
theorem frobeniusSchurIndicator_fdRep_ofShrink_two {W : Type w} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (ρ : Representation k G W) :
    frobeniusSchurIndicator k (FDRep.ofShrink ρ) 2 = Representation.frobeniusSchurIndicator ρ := by
  rw [frobeniusSchurIndicator_fdRep_two, FDRep.frobeniusSchurIndicator_def]
  exact Representation.frobeniusSchurIndicator_eq_of_equiv (FDRep.ofShrinkEquiv ρ)

end Two

end TauCeti

namespace FDRep

variable {k : Type} {G : Type v} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
  [Invertible (Nat.card G : k)] (V : FDRep k G) [Simple V]

/-- Over any algebraically closed field in which `|G|` is invertible (characteristic two included
when `|G|` is odd), the Frobenius–Schur indicator of a simple `V : FDRep k G` takes only the values
`1`, `0`, or `-1`. -/
theorem frobeniusSchurIndicator_eq_one_or_eq_zero_or_eq_neg_one :
    FDRep.frobeniusSchurIndicator V = 1 ∨ FDRep.frobeniusSchurIndicator V = 0 ∨
      FDRep.frobeniusSchurIndicator V = -1 := by
  rw [← TauCeti.frobeniusSchurIndicator_fdRep_two]
  exact TauCeti.frobeniusSchurIndicator_two_eq_one_or_eq_zero_or_eq_neg_one k V

/-- Over an algebraically closed field in which `|G|` is invertible, the Frobenius–Schur indicator
of a simple representation `V : FDRep k G` is nonzero if and only if `V` is isomorphic to its dual
`Vᘁ`. -/
theorem frobeniusSchurIndicator_ne_zero_iff :
    FDRep.frobeniusSchurIndicator V ≠ 0 ↔ Nonempty (V ≅ Vᘁ) := by
  rw [← TauCeti.frobeniusSchurIndicator_fdRep_two]
  exact TauCeti.frobeniusSchurIndicator_two_ne_zero_iff k V

/-- Over an algebraically closed field in which `|G|` is invertible, the Frobenius–Schur indicator
of a simple representation `V : FDRep k G` is zero if and only if `V` is not isomorphic to its dual
`Vᘁ`. -/
theorem frobeniusSchurIndicator_eq_zero_iff :
    FDRep.frobeniusSchurIndicator V = 0 ↔ IsEmpty (V ≅ Vᘁ) := by
  rw [← TauCeti.frobeniusSchurIndicator_fdRep_two]
  exact TauCeti.frobeniusSchurIndicator_two_eq_zero_iff k V

end FDRep
