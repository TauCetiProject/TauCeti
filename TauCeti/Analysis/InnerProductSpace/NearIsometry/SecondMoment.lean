/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.NearIsometry.Basic
public import TauCeti.Algebra.Module.LinearMap.BigOperators
public import TauCeti.LinearAlgebra.Spreading
public import TauCeti.RepresentationTheory.Unitary

/-!
# One translate from a second moment

Let a finite group `Γ` act unitarily on a finite-dimensional inner product space `T` by `ρ`, let
`T₀ ⊆ T` be a subspace whose orthogonal projection `pr₀` commutes with every `ρ s`, and let
`B : S → T` be linear. Suppose that `pr₀ B` is a near isometry with error `ε` and that the second
moment of the operators `B† ρ(s) B` is nearly as small as Cauchy–Schwarz allows:
`dim T₀ · ∑_s ‖B† ρ(s) B‖² ≤ #Γ (1 + ε) (dim S)²`. Then the translates `pr₀ ρ(s) B : S → T₀`
spread with error `3ε/2` (`TauCeti.IsSpread`): for every subspace `F ⊆ T₀` of share `α`, the
preimage of `F` under one of them has dimension at most `((1 + α) / 2 + 3ε/2) dim S`.

Here `‖·‖` is the Frobenius (Hilbert–Schmidt) seminorm. The proof: `s ↦ ‖pr_F ρ(s) B‖²` is the
Hilbert–Schmidt inner product of `pr_F` with `ρ(s) B B† ρ(s)⁻¹`, and the Gram matrix of these
operators is `(‖B† ρ(s⁻¹ t) B‖²)_{s,t}`, so Cauchy–Schwarz bounds the mean of `‖pr_F ρ(s) B‖²` by
`(α + 1 + ε) / 2 · dim S`. One `s` is at most the mean, and on the preimage of `F` the near
isometry turns that bound into a bound for the dimension.

## Main results

* `TauCeti.sum_trace_adjoint_comp_eq_card_mul_sum_sq_frobenius`: the Gram identity
  `∑_{s,t} tr ((ρ(s) B B† ρ(s)⁻¹)† ρ(t) B B† ρ(t)⁻¹) = #Γ ∑_s ‖B† ρ(s) B‖²`.
* `TauCeti.sq_sum_sq_frobenius_starProjection_comp_le`: Cauchy–Schwarz,
  `(∑_s ‖pr_F ρ(s) B‖²)² ≤ dim F · #Γ ∑_s ‖B† ρ(s) B‖²`.
* `TauCeti.isSpread_of_sum_sq_frobenius_le`: the translates `pr₀ ρ(s) B` spread with error
  `3ε/2`.

## References

These results are adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0,
Copyright 2026 Anthropic PBC), file `src/New/Spanning/SecondMoment/FewTranslates.lean`
(`New.inner_hilbertSchmidtVector_translate`, `New.sq_sum_hilbertSchmidtNorm_orthoProj_comp_le`,
`New.isSpread_of_second_moment`), where they are stated over `ℂ` through an embedding of linear
maps into a Euclidean space; here the Hilbert–Schmidt inner product is the trace `tr (X† Y)` and
the field is any `RCLike` field. The method, rank bounds from second moments of frames, goes back
to L. R. Welch, *Lower bounds on the maximum cross correlation of signals*, IEEE Trans. Inform.
Theory 20 (1974), 397–399.
-/

public section

open Module LinearMap TauCeti TauCeti.UnitarilyInvariantSeminorm Finset

open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 S T Γ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup S] [InnerProductSpace 𝕜 S] [FiniteDimensional 𝕜 S]
  [NormedAddCommGroup T] [InnerProductSpace 𝕜 T] [FiniteDimensional 𝕜 T]
  [Group Γ] {ρ : Representation 𝕜 Γ T}

/-- **Gram entries of the translates.** For a norm-preserving representation `ρ`, the
Hilbert–Schmidt inner product of `ρ(s) B B† ρ(s)⁻¹` and `ρ(t) B B† ρ(t)⁻¹` is the squared
Frobenius seminorm of `B† ρ(s⁻¹ t) B`. -/
theorem trace_adjoint_comp_eq_sq_frobenius_adjoint_comp_comp (hρ : ∀ s x, ‖ρ s x‖ = ‖x‖)
    (B : S →ₗ[𝕜] T) (s t : Γ) :
    trace 𝕜 T (((ρ s ∘ₗ B) ∘ₗ (ρ s ∘ₗ B).adjoint).adjoint ∘ₗ ((ρ t ∘ₗ B) ∘ₗ (ρ t ∘ₗ B).adjoint)) =
      ((UnitarilyInvariantSeminorm.frobenius 𝕜 S S (B.adjoint ∘ₗ ρ (s⁻¹ * t) ∘ₗ B) ^ 2 : ℝ) :
        𝕜) := by
  set X : S →ₗ[𝕜] T := ρ s ∘ₗ B
  set Y : S →ₗ[𝕜] T := ρ t ∘ₗ B
  have h_factor : B.adjoint ∘ₗ ρ (s⁻¹ * t) ∘ₗ B = X.adjoint ∘ₗ Y := by
    simp [X, Y, adjoint_comp, ρ.adjoint_eq_inv hρ, Module.End.mul_eq_comp, comp_assoc]
  rw [h_factor, sq_frobenius_eq_trace]
  calc trace 𝕜 T ((X ∘ₗ X.adjoint).adjoint ∘ₗ Y ∘ₗ Y.adjoint)
      = trace 𝕜 T (((X ∘ₗ X.adjoint) ∘ₗ Y) ∘ₗ Y.adjoint) := by
        rw [adjoint_comp, adjoint_adjoint, comp_assoc _ Y]
    _ = trace 𝕜 S (Y.adjoint ∘ₗ (X ∘ₗ X.adjoint) ∘ₗ Y) := trace_comp_comm' _ _
    _ = trace 𝕜 S ((X.adjoint ∘ₗ Y).adjoint ∘ₗ X.adjoint ∘ₗ Y) := by
        simp only [adjoint_comp, adjoint_adjoint, comp_assoc]

/-- **The Gram identity.** Summed over all pairs, the Hilbert–Schmidt inner products of the
translates `ρ(s) B B† ρ(s)⁻¹` give `#Γ` times the second moment `∑_s ‖B† ρ(s) B‖²`. -/
theorem sum_trace_adjoint_comp_eq_card_mul_sum_sq_frobenius [Fintype Γ]
    (hρ : ∀ s x, ‖ρ s x‖ = ‖x‖) (B : S →ₗ[𝕜] T) :
    trace 𝕜 T ((∑ s : Γ, (ρ s ∘ₗ B) ∘ₗ (ρ s ∘ₗ B).adjoint).adjoint ∘ₗ
        ∑ t : Γ, (ρ t ∘ₗ B) ∘ₗ (ρ t ∘ₗ B).adjoint) =
      ((Fintype.card Γ * ∑ s : Γ,
        UnitarilyInvariantSeminorm.frobenius 𝕜 S S (B.adjoint ∘ₗ ρ s ∘ₗ B) ^ 2 : ℝ) : 𝕜) := by
  simp_rw [map_sum, LinearMap.finsetSum_comp, LinearMap.comp_finsetSum, map_sum,
    trace_adjoint_comp_eq_sq_frobenius_adjoint_comp_comp hρ]
  -- For each `s`, the map `t ↦ s⁻¹ * t` is a bijection of `Γ`.
  have h_row (s : Γ) : ∑ t : Γ, ((UnitarilyInvariantSeminorm.frobenius 𝕜 S S
      (B.adjoint ∘ₗ ρ (s⁻¹ * t) ∘ₗ B) ^ 2 : ℝ) : 𝕜) = ∑ u : Γ,
        ((UnitarilyInvariantSeminorm.frobenius 𝕜 S S (B.adjoint ∘ₗ ρ u ∘ₗ B) ^ 2 : ℝ) : 𝕜) :=
    (Group.mulLeft_bijective s⁻¹).sum_comp fun u ↦
      ((UnitarilyInvariantSeminorm.frobenius 𝕜 S S (B.adjoint ∘ₗ ρ u ∘ₗ B) ^ 2 : ℝ) : 𝕜)
  rw [Fintype.sum_congr _ _ h_row, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    RCLike.ofReal_mul, RCLike.ofReal_natCast, RCLike.ofReal_sum]

/-- **Cauchy–Schwarz for the translates.** For a finite group acting by norm-preserving
operators and a subspace `F` of the target, `(∑_s ‖pr_F ρ(s) B‖²)² ≤ dim F · #Γ ∑_s ‖B† ρ(s) B‖²`.
-/
theorem sq_sum_sq_frobenius_starProjection_comp_le [Fintype Γ] (hρ : ∀ s x, ‖ρ s x‖ = ‖x‖)
    (B : S →ₗ[𝕜] T) (F : Submodule 𝕜 T) :
    (∑ s : Γ, UnitarilyInvariantSeminorm.frobenius 𝕜 S T
        ((F.starProjection : T →ₗ[𝕜] T) ∘ₗ ρ s ∘ₗ B) ^ 2) ^ 2 ≤
      finrank 𝕜 F * (Fintype.card Γ *
        ∑ s : Γ, UnitarilyInvariantSeminorm.frobenius 𝕜 S S (B.adjoint ∘ₗ ρ s ∘ₗ B) ^ 2) := by
  set p : T →ₗ[𝕜] T := (F.starProjection : T →ₗ[𝕜] T)
  set X : T →ₗ[𝕜] T := ∑ s : Γ, (ρ s ∘ₗ B) ∘ₗ (ρ s ∘ₗ B).adjoint
  have h_norm : UnitarilyInvariantSeminorm.frobenius 𝕜 T T X ^ 2 = Fintype.card Γ * ∑ s : Γ,
      UnitarilyInvariantSeminorm.frobenius 𝕜 S S (B.adjoint ∘ₗ ρ s ∘ₗ B) ^ 2 :=
    RCLike.ofReal_injective (K := 𝕜) <| by
      rw [sq_frobenius_eq_trace, sum_trace_adjoint_comp_eq_card_mul_sum_sq_frobenius hρ]
  have h_inner : ∑ s : Γ, UnitarilyInvariantSeminorm.frobenius 𝕜 S T (p ∘ₗ ρ s ∘ₗ B) ^ 2 =
      RCLike.re (trace 𝕜 T (p.adjoint ∘ₗ X)) := by
    rw [LinearMap.comp_finsetSum, map_sum, map_sum]
    refine Fintype.sum_congr _ _ fun s ↦ ?_
    rw [← sq_frobenius_starProjection_comp, RCLike.ofReal_re]
  have h_cs := re_trace_adjoint_comp_le p X
  calc (∑ s : Γ, UnitarilyInvariantSeminorm.frobenius 𝕜 S T (p ∘ₗ ρ s ∘ₗ B) ^ 2) ^ 2
      ≤ (UnitarilyInvariantSeminorm.frobenius 𝕜 T T p *
          UnitarilyInvariantSeminorm.frobenius 𝕜 T T X) ^ 2 :=
        pow_le_pow_left₀ (sum_nonneg fun _ _ ↦ sq_nonneg _) (h_inner.trans_le h_cs) 2
    _ = _ := by rw [mul_pow, sq_frobenius_starProjection, h_norm]

/-- The mean bound of the second-moment argument: if
`dim T₀ · ∑_s ‖B† ρ(s) B‖² ≤ #Γ (1 + ε) (dim S)²` and `F ⊆ T` has dimension `α dim T₀`, then
`∑_s ‖pr_F ρ(s) B‖² ≤ #Γ · (α + 1 + ε) / 2 · dim S`. -/
private theorem sum_sq_frobenius_starProjection_comp_le [Fintype Γ] (hρ : ∀ s x, ‖ρ s x‖ = ‖x‖)
    {B : S →ₗ[𝕜] T} {ε α d : ℝ} (hε : 0 ≤ ε) (hα : 0 ≤ α)
    (h_moment : d * ∑ s : Γ,
      UnitarilyInvariantSeminorm.frobenius 𝕜 S S (B.adjoint ∘ₗ ρ s ∘ₗ B) ^ 2 ≤
        Fintype.card Γ * ((1 + ε) * finrank 𝕜 S ^ 2))
    (F : Submodule 𝕜 T) (hF : (finrank 𝕜 F : ℝ) = α * d) :
    ∑ s : Γ, UnitarilyInvariantSeminorm.frobenius 𝕜 S T
        ((F.starProjection : T →ₗ[𝕜] T) ∘ₗ ρ s ∘ₗ B) ^ 2 ≤
      Fintype.card Γ * ((α + 1 + ε) / 2 * finrank 𝕜 S) := by
  set moment : ℝ := ∑ s : Γ,
    UnitarilyInvariantSeminorm.frobenius 𝕜 S S (B.adjoint ∘ₗ ρ s ∘ₗ B) ^ 2
  refine (abs_le_of_sq_le_sq' ?_ (by positivity)).2
  calc (∑ s : Γ, UnitarilyInvariantSeminorm.frobenius 𝕜 S T
          ((F.starProjection : T →ₗ[𝕜] T) ∘ₗ ρ s ∘ₗ B) ^ 2) ^ 2
      ≤ finrank 𝕜 F * (Fintype.card Γ * moment) :=
        sq_sum_sq_frobenius_starProjection_comp_le hρ B F
    _ = α * Fintype.card Γ * (d * moment) := by rw [hF]; ring
    _ ≤ α * Fintype.card Γ * (Fintype.card Γ * ((1 + ε) * finrank 𝕜 S ^ 2)) := by gcongr
    _ = α * (1 + ε) * (Fintype.card Γ * finrank 𝕜 S) ^ 2 := by ring
    _ ≤ ((α + 1 + ε) / 2) ^ 2 * (Fintype.card Γ * finrank 𝕜 S) ^ 2 := by
        gcongr
        nlinarith [sq_nonneg (α - (1 + ε))]
    _ = (Fintype.card Γ * ((α + 1 + ε) / 2 * finrank 𝕜 S)) ^ 2 := by ring

omit [FiniteDimensional 𝕜 S] in
/-- On the preimage of `F₀ ⊆ T₀` under `pr₀ ρ(s) B`, the maps `pr₀ B` and `pr_F ρ(s) B` have equal
pointwise norms, where `F` is `F₀` as a subspace of `T`. -/
private theorem norm_orthogonalProjectionOnto_apply_eq (hρ : ∀ s x, ‖ρ s x‖ = ‖x‖)
    {T₀ : Submodule 𝕜 T}
    (h_comm : ∀ s x, T₀.starProjection (ρ s x) = ρ s (T₀.starProjection x))
    (B : S →ₗ[𝕜] T) (F₀ : Submodule 𝕜 T₀) (s : Γ) {x : S}
    (hx : x ∈ F₀.comap ((T₀.orthogonalProjectionOnto : T →ₗ[𝕜] T₀) ∘ₗ ρ s ∘ₗ B)) :
    ‖T₀.orthogonalProjectionOnto (B x)‖ =
      ‖(F₀.map T₀.subtype).starProjection (ρ s (B x))‖ := by
  set F : Submodule 𝕜 T := F₀.map T₀.subtype
  have hF : F ≤ T₀ := Submodule.map_subtype_le T₀ F₀
  have h_mem : T₀.starProjection (ρ s (B x)) ∈ F := Submodule.mem_map_of_mem hx
  have h_eq : F.starProjection (ρ s (B x)) = T₀.starProjection (ρ s (B x)) := by
    rw [← Submodule.starProjection_comp_starProjection_of_le hF, ContinuousLinearMap.comp_apply,
      Submodule.starProjection_eq_self_iff.2 h_mem]
  rw [h_eq, h_comm, hρ, Submodule.starProjection_apply, Submodule.norm_coe]

/-- **One translate from a second moment.** Let a finite group `Γ` act on `T` by norm-preserving
operators `ρ s`, let `T₀ ⊆ T` be a subspace whose orthogonal projection `pr₀` commutes with every
`ρ s`, and let `B : S → T` be linear with `ε ≥ 0`. Suppose that `pr₀ B : S → T₀` is a near isometry
with error `ε` and that `dim T₀ · ∑_s ‖B† ρ(s) B‖² ≤ #Γ (1 + ε) (dim S)²`. Then the family of maps
`pr₀ ρ(s) B : S → T₀`, `s ∈ Γ`, spreads with error `3ε/2`. -/
theorem isSpread_of_sum_sq_frobenius_le [Fintype Γ] (hρ : ∀ s x, ‖ρ s x‖ = ‖x‖)
    {T₀ : Submodule 𝕜 T}
    (h_comm : ∀ s x, T₀.starProjection (ρ s x) = ρ s (T₀.starProjection x))
    {B : S →ₗ[𝕜] T} {ε : ℝ} (hε : 0 ≤ ε)
    (h_isom : ((T₀.orthogonalProjectionOnto : T →ₗ[𝕜] T₀) ∘ₗ B).IsNearIsometry ε)
    (h_moment : finrank 𝕜 T₀ * ∑ s : Γ,
      UnitarilyInvariantSeminorm.frobenius 𝕜 S S (B.adjoint ∘ₗ ρ s ∘ₗ B) ^ 2 ≤
        Fintype.card Γ * ((1 + ε) * finrank 𝕜 S ^ 2)) :
    IsSpread (fun s : Γ ↦ (T₀.orthogonalProjectionOnto : T →ₗ[𝕜] T₀) ∘ₗ ρ s ∘ₗ B)
      (3 / 2 * ε) := by
  refine isSpread_iff.2 fun F₀ ↦ ?_
  set F : Submodule 𝕜 T := F₀.map T₀.subtype
  set α : ℝ := finrank 𝕜 F₀ / finrank 𝕜 T₀
  have hα : 0 ≤ α := by positivity
  have h_dim : (finrank 𝕜 F : ℝ) = α * finrank 𝕜 T₀ := by
    rw [Submodule.finrank_map_subtype_eq]
    rcases eq_or_ne (finrank 𝕜 T₀ : ℝ) 0 with h | h
    · have h_zero : finrank 𝕜 F₀ = 0 :=
        Nat.eq_zero_of_le_zero (F₀.finrank_le.trans_eq (by exact_mod_cast h))
      simp [h_zero, h]
    · exact (div_mul_cancel₀ _ h).symm
  -- Some translate has `‖pr_F ρ(s) B‖²` at most the mean bound.
  have h_mean := sum_sq_frobenius_starProjection_comp_le hρ hε hα h_moment F h_dim
  obtain ⟨s, -, hs⟩ : ∃ s ∈ (Finset.univ : Finset Γ), UnitarilyInvariantSeminorm.frobenius 𝕜 S T
      ((F.starProjection : T →ₗ[𝕜] T) ∘ₗ ρ s ∘ₗ B) ^ 2 ≤ (α + 1 + ε) / 2 * finrank 𝕜 S :=
    exists_le_of_sum_le univ_nonempty (by rwa [sum_const, card_univ, nsmul_eq_mul])
  refine ⟨s, ?_⟩
  set W' : Submodule 𝕜 S := F₀.comap ((T₀.orthogonalProjectionOnto : T →ₗ[𝕜] T₀) ∘ₗ ρ s ∘ₗ B)
  -- On the preimage `W'` the near isometry is controlled by `‖pr_F ρ(s) B‖`.
  have h_preimage : UnitarilyInvariantSeminorm.frobenius 𝕜 S T₀
      (((T₀.orthogonalProjectionOnto : T →ₗ[𝕜] T₀) ∘ₗ B) ∘ₗ (W'.starProjection : S →ₗ[𝕜] S)) ≤
        UnitarilyInvariantSeminorm.frobenius 𝕜 S T
          ((F.starProjection : T →ₗ[𝕜] T) ∘ₗ ρ s ∘ₗ B) := by
    refine (frobenius_le_frobenius_of_norm_le fun x ↦ ?_).trans
      (frobenius_comp_starProjection_le _ W')
    exact (norm_orthogonalProjectionOnto_apply_eq hρ h_comm B F₀ s
      (W'.starProjection_apply_mem x)).le
  have h_near := isNearIsometry_iff.1 h_isom W'
  have h_sq := pow_le_pow_left₀ (apply_nonneg _ _) h_preimage 2
  have h_goal : (finrank 𝕜 W' : ℝ) ≤ ((1 + α) / 2 + 3 / 2 * ε) * finrank 𝕜 S := by linarith
  exact h_goal

end TauCeti
