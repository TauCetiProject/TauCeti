/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.GroupTheory.Coset.Basic
public import TauCeti.RepresentationTheory.Continuous.AlmostInvariant
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic

/-!
# Representations induced from subgroups of finite index

Let `K` be a subgroup of finite index in a group `G` and `π` a representation of `K` on a normed
space `V`. The induced representation `ContRepresentation.induced π` of `G` acts on the space
`PiLp 2 (fun _ : G ⧸ K ↦ V)` of `V`-valued functions on the cosets, with the `L²` norm, by

`(induced π g f) (g • x) = π (outCocycle g x) (f x)`,

where `QuotientGroup.outCocycle g x = (g • x).out⁻¹ * g * x.out ∈ K` is the cocycle of the
translation action relative to the chosen coset representatives. This is the usual model of
`Ind_K^G π` as functions `φ : G → V` with `φ (g * k) = π k⁻¹ (φ g)`, read off on the chosen
representatives.

Induction from a subgroup of finite index preserves unitarity and almost invariant vectors: an
almost invariant unit vector `ξ` of `π` spread evenly over the cosets is almost invariant for
`induced π`, since the finitely many cocycle values of a finite set of elements move `ξ` only a
little. In the other direction, a vector `f` fixed by a normal subgroup `Λ` of `G` has each of its
values `f x` fixed by `Λ ∩ K`. These two facts transfer relative property (T) from a group to its
subgroups of finite index.

## Main declarations

* `ContRepresentation.induced`: the representation induced from a subgroup of finite index.
* `ContRepresentation.induced_apply_smul`: its defining formula.
* `ContRepresentation.isUnitary_induced`: induction preserves unitarity.
* `ContRepresentation.hasAlmostInvariantVectors_induced`: induction preserves almost invariant
  vectors.
* `ContRepresentation.apply_mem_invariants_of_mem_invariants_induced`: the values of a vector of
  `induced π` fixed by a normal subgroup `Λ` are fixed by `Λ ∩ K`.

## References

* B. Bekka, P. de la Harpe and A. Valette, *Kazhdan's Property (T)*, Cambridge University Press
  (2008), §E.1 and Theorem 1.7.1.
-/

public section

noncomputable section

open QuotientGroup

namespace ContRepresentation

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {K : Subgroup G} [Fintype (G ⧸ K)]

/-- The operator by which `g` acts on the induced representation. -/
private def inducedOp (π : ContRepresentation 𝕜 K V) (g : G) :
    (PiLp 2 fun _ : G ⧸ K ↦ V) →L[𝕜] PiLp 2 fun _ : G ⧸ K ↦ V :=
  (PiLp.continuousLinearEquiv 2 𝕜 fun _ : G ⧸ K ↦ V).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun y ↦
      π (outCocycle g (g⁻¹ • y)) ∘L PiLp.proj 2 (fun _ : G ⧸ K ↦ V) (g⁻¹ • y)

omit [Fintype (G ⧸ K)] in
private theorem inducedOp_apply (π : ContRepresentation 𝕜 K V) (g : G)
    (f : PiLp 2 fun _ : G ⧸ K ↦ V) (y : G ⧸ K) :
    inducedOp π g f y = π (outCocycle g (g⁻¹ • y)) (f (g⁻¹ • y)) :=
  (rfl)

/-- The representation of `G` induced from a representation `π` of a subgroup `K` of finite
index: `G` acts on `V`-valued functions on `G ⧸ K` by
`(induced π g f) (g • x) = π (outCocycle g x) (f x)`. -/
def induced (π : ContRepresentation 𝕜 K V) : ContRepresentation 𝕜 G (PiLp 2 fun _ : G ⧸ K ↦ V) :=
  .ofMonoidHom
    { toFun := inducedOp π
      map_one' := by
        ext f y
        simp [inducedOp_apply]
      map_mul' g h := by
        ext f y
        simp [inducedOp_apply, outCocycle_mul, mul_smul] }

variable (π : ContRepresentation 𝕜 K V)

/-- The value of `induced π g f` at a coset `y`. -/
theorem induced_apply_apply (g : G) (f : PiLp 2 fun _ : G ⧸ K ↦ V) (y : G ⧸ K) :
    induced π g f y = π (outCocycle g (g⁻¹ • y)) (f (g⁻¹ • y)) :=
  (rfl)

/-- The defining formula of the induced representation: `g` carries the value of `f` at `x`, twisted
by the cocycle, to the coset `g • x`. -/
@[simp]
theorem induced_apply_smul (g : G) (f : PiLp 2 fun _ : G ⧸ K ↦ V) (x : G ⧸ K) :
    induced π g f (g • x) = π (outCocycle g x) (f x) := by
  rw [induced_apply_apply, inv_smul_smul]

/-- A vector of the induced representation is fixed by `g` exactly when `g` carries its value at
each coset `x`, twisted by the cocycle, to its value at `g • x`. -/
theorem induced_apply_eq_self_iff (g : G) (f : PiLp 2 fun _ : G ⧸ K ↦ V) :
    induced π g f = f ↔ ∀ x, f (g • x) = π (outCocycle g x) (f x) := by
  refine ⟨fun h x ↦ by rw [← induced_apply_smul, h], fun h ↦ ?_⟩
  ext y
  rw [induced_apply_apply, ← h, smul_inv_smul]

/-- If a vector of the induced representation is fixed by every element of a normal subgroup `Λ`
of `G`, then each of its values is fixed by `Λ ∩ K`. -/
theorem apply_mem_invariants_of_mem_invariants_induced {Λ : Subgroup G} [Λ.Normal]
    {f : PiLp 2 fun _ : G ⧸ K ↦ V} (hf : f ∈ ((induced π).restrict Λ.subtype).invariants)
    (x : G ⧸ K) : f x ∈ (π.restrict (Λ.subgroupOf K).subtype).invariants := by
  rintro ⟨k, hk⟩
  -- The conjugate `l = x.out * k * x.out⁻¹` lies in `Λ`, fixes the coset `x` and has cocycle `k`
  -- there, so the fixed-point equation of `f` at `l` and `x` reads `f x = π k (f x)`.
  set l : G := x.out * k * x.out⁻¹
  have hl : l ∈ Λ := ‹Λ.Normal›.conj_mem _ (Subgroup.mem_subgroupOf.mp hk) _
  have hlx : l • x = x := by
    conv_lhs => rw [← out_eq' x]
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, show l * x.out = x.out * k by simp [l],
      mk_mul_of_mem _ k.property, out_eq']
  have hc : outCocycle l x = k := by
    ext
    rw [coe_outCocycle, hlx]
    simp [l, mul_assoc]
  have hfx := (induced_apply_eq_self_iff π l f).mp (hf ⟨l, hl⟩) x
  rw [hlx, hc] at hfx
  exact hfx.symm

variable {π} in
/-- Induction from a subgroup of finite index preserves almost invariant vectors: an almost
invariant unit vector, spread evenly over the cosets, is almost invariant for the induced
representation. -/
theorem hasAlmostInvariantVectors_induced (h : π.HasAlmostInvariantVectors) :
    (induced π).HasAlmostInvariantVectors := by
  classical
  refine (hasAlmostInvariantVectors_def _).mpr fun F ε hε ↦ ?_
  -- Choose `ξ` almost invariant under the finitely many cocycle values of elements of `F`.
  obtain ⟨ξ, hξ1, hξ⟩ := (hasAlmostInvariantVectors_def π).mp h
    ((F ×ˢ Finset.univ).image fun p ↦ outCocycle p.1 p.2) ε hε
  have hn : (0 : ℝ) < Fintype.card (G ⧸ K) := Nat.cast_pos.mpr Fintype.card_pos
  set c : ℝ := (Real.sqrt (Fintype.card (G ⧸ K)))⁻¹
  have hc : c ^ 2 * Fintype.card (G ⧸ K) = 1 := by
    rw [inv_pow, Real.sq_sqrt hn.le, inv_mul_cancel₀ hn.ne']
  have hc0 : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hn)
  refine ⟨WithLp.toLp 2 fun _ ↦ (c : 𝕜) • ξ, ?_, fun g hg ↦ ?_⟩
  · have h2 : ‖WithLp.toLp 2 fun _ : G ⧸ K ↦ (c : 𝕜) • ξ‖ ^ 2 = 1 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp [norm_smul, hξ1, abs_of_pos hc0, mul_comm _ (c ^ 2), hc]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2
  · have h2 : ‖induced π g (WithLp.toLp 2 fun _ : G ⧸ K ↦ (c : 𝕜) • ξ) -
        WithLp.toLp 2 fun _ ↦ (c : 𝕜) • ξ‖ ^ 2 < ε ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp only [PiLp.sub_apply, induced_apply_apply, map_smul, ← smul_sub, norm_smul,
        RCLike.norm_ofReal, abs_of_pos hc0, mul_pow]
      calc ∑ y : G ⧸ K, c ^ 2 * ‖π (outCocycle g (g⁻¹ • y)) ξ - ξ‖ ^ 2
          < ∑ _y : G ⧸ K, c ^ 2 * ε ^ 2 := by
            refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun y _ ↦ ?_
            refine mul_lt_mul_of_pos_left ?_ (by positivity)
            refine pow_lt_pow_left₀ (hξ _ ?_) (norm_nonneg _) two_ne_zero
            exact Finset.mem_image.mpr ⟨(g, g⁻¹ • y), by simp [hg], rfl⟩
        _ = ε ^ 2 := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            linear_combination ε ^ 2 * hc
    exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp h2

section Unitary

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  {K : Subgroup G} [Fintype (G ⧸ K)] {π : ContRepresentation 𝕜 K V}

/-- Induction from a subgroup of finite index preserves unitarity. -/
theorem isUnitary_induced (hπ : π.IsUnitary) : (induced π).IsUnitary := by
  refine (isUnitary_iff_norm_map _).mpr fun g f ↦ ?_
  have h : ‖induced π g f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp_rw [induced_apply_apply, hπ.norm_map]
    exact Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ fun y ↦ rfl
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

end Unitary

end ContRepresentation
