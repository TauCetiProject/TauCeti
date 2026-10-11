/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.RepresentationTheory.Coinvariants
public import TauCeti.RepresentationTheory.NormSplit.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.RepresentationTheory.PGroupInvariants

/-!
# Representations of `p`-groups with vanishing degree `-1` Tate cohomology

Let `G` be a finite `p`-group and `ρ` a representation of `G` on a vector space `V` over a field
of characteristic `p`. If every vector of norm zero lies in the augmentation submodule — that is,
if the degree `-1` Tate cohomology of `G` with coefficients in `V` vanishes — then the identity of
`V` is a norm
`x ↦ ∑ g, ρ g (φ (ρ g⁻¹ x))` for the conjugation action of `G` on `End(V)`
(Serre, *Local Fields*, IX §3, Theorem 4; Brown, *Cohomology of Groups*, VI 8.5). No finiteness is
assumed on `V`. In the theorem of Nakayama and Rim, this provides the identity-norm condition
in characteristic `p`, which `Representation.id_mem_range_norm_linHom_of_baseChange` then lifts.

## Main statements

* `Representation.id_mem_range_norm_linHom_of_ker_norm_le`: for a finite `p`-group in
  characteristic `p`, if the kernel of the norm lies in the augmentation submodule, then the
  identity is a norm for the conjugation action on `End(V)`.

## References

* J.-P. Serre, *Local Fields*, Chapter IX, §3.
* K. S. Brown, *Cohomology of Groups*, Chapter VI, §8.
-/

public section

namespace Representation

variable {F G V : Type*} [Field F] [Group G] [Fintype G] [AddCommGroup V] [Module F V]
  (p : ℕ) [Fact p.Prime] [CharP F p]

/-- **A representation of a `p`-group in characteristic `p` with vanishing degree `-1` Tate
cohomology has the identity as a norm.** If `G` is a finite `p`-group, `F` has characteristic `p`,
and every vector of `V` of norm zero lies in the augmentation submodule, then the identity is the
norm
`∑ g, ρ g ∘ φ ∘ ρ g⁻¹` of an `F`-linear `φ`. -/
theorem id_mem_range_norm_linHom_of_ker_norm_le (hG : IsPGroup p G) (ρ : Representation F G V)
    (h : LinearMap.ker ρ.norm ≤ Coinvariants.ker ρ) :
    LinearMap.id ∈ LinearMap.range (linHom ρ ρ).norm := by
  classical
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (Coinvariants.ker ρ)
  -- The coinduced action of `G` on `G → W`.
  let σ : Representation F G (G → W) :=
    { toFun h := LinearMap.funLeft F W (h⁻¹ * ·)
      map_one' := by ext; simp
      map_mul' a b := by ext; simp [mul_assoc] }
  have hσ (h : G) (w : G → W) (g : G) : σ h w g = w (h⁻¹ * g) := rfl
  let f : (G → W) →ₗ[F] V := ∑ g : G, ρ g ∘ₗ W.subtype ∘ₗ LinearMap.proj g
  have hf (w : G → W) : f w = ∑ g : G, ρ g (w g) := by simp [f]
  have hfσ (h : G) (w : G → W) : f (σ h w) = ρ h (f w) := by
    rw [hf, hf, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun g ↦ ?_
    simp [hσ, ← Module.End.mul_apply, ← map_mul]
  -- `f` is injective: a fixed vector of its kernel is constant with value of norm zero in `W`.
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hK
    have hKs (g : G) : LinearMap.ker f ≤ (LinearMap.ker f).comap (σ g) := fun w hw ↦ by
      simp only [Submodule.mem_comap, LinearMap.mem_ker] at hw ⊢
      rw [hfσ, hw, map_zero]
    have : Nontrivial (LinearMap.ker f) := Submodule.nontrivial_iff_ne_bot.2 hK
    obtain ⟨y, hy0, hy⟩ :=
      (σ.subrepresentation _ hKs).exists_ne_zero_apply_eq_self_of_forall_pow_eq_one p
        fun g ↦ (hG g).imp fun _ hn ↦ by rw [← map_pow, hn, map_one]
    have hconst (g : G) : (y : G → W) g = (y : G → W) 1 := by
      have := congrFun (congrArg Subtype.val (hy g⁻¹)) 1
      simpa [hσ] using this
    have hnorm : ρ.norm ((y : G → W) 1 : V) = 0 := by
      have := y.2
      rw [LinearMap.mem_ker, hf] at this
      simpa [Representation.norm, hconst] using this
    have hmem : ((y : G → W) 1 : V) ∈ Coinvariants.ker ρ ⊓ W := ⟨h hnorm, ((y : G → W) 1).2⟩
    rw [hW.inf_eq_bot, Submodule.mem_bot] at hmem
    exact hy0 (Subtype.ext (funext fun g ↦ Subtype.ext (by simpa [hconst g] using hmem)))
  -- `f` is surjective: a fixed functional on its cokernel kills `W` and the augmentation
  -- submodule.
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]
    by_contra hX
    have hXs (g : G) : LinearMap.range f ≤ (LinearMap.range f).comap (ρ g) := by
      rintro _ ⟨w, rfl⟩
      exact ⟨σ g w, hfσ g w⟩
    let τ := ρ.quotient _ hXs
    have : Nontrivial (V ⧸ LinearMap.range f) :=
      Submodule.Quotient.nontrivial_iff.2 hX
    obtain ⟨l, hl0, hl⟩ := τ.dual.exists_ne_zero_apply_eq_self_of_forall_pow_eq_one p
        fun g ↦ (hG g).imp fun _ hn ↦ by rw [← map_pow, hn, map_one]
    have hl' (g : G) (v : V) :
        l (Submodule.Quotient.mk (ρ g v)) = l (Submodule.Quotient.mk v) := by
      have := LinearMap.congr_fun (hl g⁻¹) (Submodule.Quotient.mk v)
      simpa [dual_apply, τ, Module.Dual.transpose_apply] using this
    have hker : Coinvariants.ker ρ ≤ LinearMap.ker (l ∘ₗ (LinearMap.range f).mkQ) :=
      Submodule.span_le.2 fun _ ⟨⟨g, v⟩, hv⟩ ↦ by simp [← hv, hl']
    have hW' : W ≤ LinearMap.ker (l ∘ₗ (LinearMap.range f).mkQ) := fun w hw ↦ by
      have hw' : w ∈ LinearMap.range f :=
        ⟨Pi.single 1 ⟨w, hw⟩, by simp [hf, Pi.single_apply, apply_ite]⟩
      simp [(Submodule.Quotient.mk_eq_zero _).2 hw']
    refine hl0 (LinearMap.ext fun c ↦ ?_)
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    have hv : v ∈ Coinvariants.ker ρ ⊔ W := hW.sup_eq_top ▸ Submodule.mem_top
    exact sup_le hker hW' hv
  -- The identity is the norm of the projection onto the summand at `1`.
  let e := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨W.subtype ∘ₗ LinearMap.proj 1 ∘ₗ e.symm.toLinearMap, LinearMap.ext fun x ↦ ?_⟩
  obtain ⟨w, rfl⟩ := hsurj x
  have he (g : G) : e.symm (ρ g⁻¹ (f w)) = σ g⁻¹ w :=
    e.symm_apply_eq.2 (hfσ g⁻¹ w).symm
  rw [norm_linHom_apply, LinearMap.id_apply]
  conv_rhs => rw [hf]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  simp [he, hσ]

end Representation
