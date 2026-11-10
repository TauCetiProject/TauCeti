/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.AtkinLehner
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.Basic
import TauCeti.Data.ZMod.Units
import TauCeti.NumberTheory.HeckeRing.GL2.AntiInvolution
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.ElementaryDivisors
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.CoprimeMul
import TauCeti.NumberTheory.HeckeRing.Multiplicity.Equiv
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# The Atkin–Lehner anti-involution of the `Γ₁(N)` Hecke pair

The anti-involution `ι(g) = w · gᵀ · w⁻¹` with `w = diag(1, N)`, which acts on entries by
`(a, b; N c, e) ↦ (a, c; N b, e)`, preserves the image of `Γ₀(N)` and the monoid `Δ₀(N)`
(`HeckeRing.GL2.atkinLehnerAntiInvolution`). It leaves both diagonal entries untouched, so it
also preserves the image of `Γ₁(N)`, cut out inside `Γ₀(N)` by the lower-right entry being
`1` modulo `N`. This file restricts it to an anti-involution of the `Γ₁(N)` Hecke pair
`(Δ₀(N), Γ₁(N))` and proves that it fixes every double coset, so that Shimura's commutativity
criterion (Proposition 3.8) applies at level `Γ₁(N)`, diamonds included.

At level `Γ₀(N)` every double coset is already fixed
(`HeckeRing.GL2.atkinLehnerAntiInvolution_bar_mem_doubleCoset`). Inside a `Γ₀(N)` double coset,
the `Γ₁(N)` double coset of a primitive element is detected by its upper-left entry modulo `N`,
which `ι` does not change. Concretely, for `x ∈ Δ₀(N)` primitive of determinant `m` with
upper-left entry `a`, choose `σ ∈ Γ₀(N)` with upper-left entry `a⁻¹` modulo `N`. Then `σ x` and
`σ ι(x)` both lie in `Γ₀(N) · diag(1, m) · Γ₀(N)` with upper-left entry `1` modulo `N`, hence in
`Γ₁(N) · diag(1, m) · Γ₁(N)` (`HeckeRing.GL2.mem_doubleCoset_Gamma1_of_mem_doubleCoset_Gamma0`).
As `σ` normalizes `Γ₁(N)`, this puts `ι(x)` in the `Γ₁(N)` double coset of `x`. A general
element of `Δ₀(N)` is a scalar multiple of a primitive one, and `ι` fixes scalars
(`HeckeRing.GL2.bar_mem_doubleCoset_of_forall_primitive`).

Since `g ↦ ι(g⁻¹)` is an automorphism of `GL₂(ℚ)` preserving `Γ₁(N)`, the symmetry of Shimura's
multiplicity also holds at inverted arguments, which is the form in which it arises for Hecke
operators acting on the left, through right-coset representatives.

## Main definitions

* `HeckeRing.GL2.atkinLehnerAntiInvolutionGamma1`: the anti-involution of the `Γ₁(N)` Hecke
  pair.
* `HeckeRing.GL2.commSemiringHeckeRingGamma1`: the commutative-semiring structure on the Hecke
  ring `R(Γ₁(N), Δ₀(N))`.

## Main results

* `HeckeRing.GL2.atkinLehnerAntiInvolutionGamma1_bar_mem_doubleCoset`: the anti-involution fixes
  the `Γ₁(N)` double coset of every element of `Δ₀(N)`.
* `HeckeRing.GL2.atkinLehnerAntiInvolutionGamma1_onHeckeCoset_eq_self`: equivalently, it acts
  trivially on `Γ₁(N) \ Δ₀(N) / Γ₁(N)`.
* `HeckeRing.GL2.atkinLehnerAutomorphism_map_Gamma1`: the automorphism `g ↦ ι(g⁻¹)` preserves
  the image of `Γ₁(N)`.
* `HeckeRing.GL2.multiplicity_inv_comm_Gamma1`: Shimura's multiplicity at level `Γ₁(N)` is
  symmetric at inverted arguments from `Δ₀(N)`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.8, and §3.3 for the double cosets of `Γ₁(N)` inside those of `Γ₀(N)`.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup DoubleCoset HeckeRing.GLn

open scoped MatrixGroups HeckeCosetModule

namespace HeckeRing.GL2

variable (N : ℕ) [NeZero N]

/-- `ι` preserves the image of `Γ₁(N)`: the image of a `Γ₁(N)` matrix lies in `Γ₀(N)`, and its
lower-right entry is that of the original matrix. -/
private lemma atkinLehnerAntiInvolution_bar_mem_Gamma1 {x : GL (Fin 2) ℚ} (hx : x ∈ Delta0 N)
    (h : x ∈ (Gamma1 N).map (mapGL ℚ)) :
    (atkinLehnerAntiInvolution N).bar x hx ∈ (Gamma1 N).map (mapGL ℚ) := by
  obtain ⟨γ, hγ, rfl⟩ := h
  obtain ⟨τ, hτ, hτeq⟩ := (atkinLehnerAntiInvolution N).bar_mem_H hx
    (Subgroup.mem_map_of_mem _ (Gamma1_in_Gamma0 N hγ))
  obtain ⟨c, hc⟩ := mem_Gamma0_iff_dvd.mp (Gamma1_in_Gamma0 N hγ)
  have hmat : (τ : Matrix (Fin 2) (Fin 2) ℤ) = !![γ 0 0, c; (N : ℤ) * γ 0 1, γ 1 1] :=
    Matrix.map_injective (Int.cast_injective (α := ℚ)) <|
      (coe_mapGL_int τ).symm.trans <| (congrArg Units.val hτeq).trans <|
        atkinLehnerAntiInvolution_bar_val N hx _ (coe_mapGL_int γ) c hc
  refine ⟨τ, mem_Gamma1_iff.mpr ⟨hτ, ?_⟩, hτeq⟩
  rw [hmat]
  simpa using (mem_Gamma1_iff.mp hγ).2

/-- The ambient Atkin–Lehner anti-involution `ι`, as a homomorphism to the opposite group. It is
written as `g ↦ ψ(g)⁻¹` through the automorphism `ψ(g) = ι(g⁻¹)` of
`HeckeRing.GL2.atkinLehnerAutomorphism`. -/
private noncomputable def atkinLehnerOpHom : GL (Fin 2) ℚ →* (GL (Fin 2) ℚ)ᵐᵒᵖ where
  toFun g := MulOpposite.op (atkinLehnerAutomorphism N g)⁻¹
  map_one' := by simp
  map_mul' a b := by simp

/-- On `Δ₀(N)` the ambient map is the anti-involution of the `Γ₀(N)` Hecke pair. -/
private lemma atkinLehnerOpHom_unop {x : GL (Fin 2) ℚ} (hx : x ∈ Delta0 N) :
    (atkinLehnerOpHom N x).unop = (atkinLehnerAntiInvolution N).bar x hx := by
  rw [← atkinLehnerAutomorphism_inv_apply N hx, map_inv]
  simp only [atkinLehnerOpHom, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op]

/-- **The Atkin–Lehner anti-involution of the `Γ₁(N)` Hecke pair**: `g ↦ w · gᵀ · w⁻¹` with
`w = diag(1, N)`, the map of `HeckeRing.GL2.atkinLehnerAntiInvolution`, which also preserves the
image of `Γ₁(N)`. -/
noncomputable def atkinLehnerAntiInvolutionGamma1 :
    HeckeAntiInvolution (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) :=
  HeckeAntiInvolution.ofAmbient (atkinLehnerOpHom N)
    (fun g ↦ by simp [atkinLehnerOpHom])
    (fun g hg ↦ by
      have hgΔ := IsHeckeTriple.mem_of_mem_left (Δ := Delta0 N) ((Gamma1 N).map (mapGL ℚ)) hg
      rw [atkinLehnerOpHom_unop N hgΔ]
      exact atkinLehnerAntiInvolution_bar_mem_Gamma1 N hgΔ hg)
    (fun g hg ↦ by
      rw [atkinLehnerOpHom_unop N hg]
      exact (atkinLehnerAntiInvolution N).bar_mem_Δ g hg)

/-- The anti-involutions of the `Γ₁(N)` and `Γ₀(N)` Hecke pairs agree on `Δ₀(N)`. -/
lemma atkinLehnerAntiInvolutionGamma1_bar_eq {x : GL (Fin 2) ℚ} (hx : x ∈ Delta0 N) :
    (atkinLehnerAntiInvolutionGamma1 N).bar x hx = (atkinLehnerAntiInvolution N).bar x hx :=
  (HeckeAntiInvolution.ofAmbient_bar _ _ _ _ x hx).trans (atkinLehnerOpHom_unop N hx)

/-- The anti-involution acts by conjugating the transpose by `w = diag(1, N)`. -/
@[simp] lemma atkinLehnerAntiInvolutionGamma1_bar {x : GL (Fin 2) ℚ} (hx : x ∈ Delta0 N) :
    (atkinLehnerAntiInvolutionGamma1 N).bar x hx =
      natDiagGL 2 ![1, N] * (GeneralLinearGroup.transposeMulEquiv (Fin 2) x).unop *
        (natDiagGL 2 ![1, N])⁻¹ := by
  rw [atkinLehnerAntiInvolutionGamma1_bar_eq, atkinLehnerAntiInvolution_bar]

/-- **The anti-involution fixes the `Γ₁(N)` double coset of a primitive element of `Δ₀(N)`.**
A matrix `σ ∈ Γ₀(N)` correcting the upper-left entry to `1` modulo `N` carries `x` and its image
into the same `Γ₁(N)` double coset of `diag(1, m)`, and it normalizes `Γ₁(N)`. -/
private lemma atkinLehnerAntiInvolutionGamma1_bar_mem_doubleCoset_of_primitive
    (x : GL (Fin 2) ℚ) (hx : x ∈ Delta0 N) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (x : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hprim : ∀ p : ℕ, p.Prime → ¬((p : ℤ) ∣ A 0 0 ∧ (p : ℤ) ∣ A 0 1 ∧ (p : ℤ) ∣ A 1 0 ∧
      (p : ℤ) ∣ A 1 1)) :
    (atkinLehnerAntiInvolutionGamma1 N).bar x hx ∈
      doubleCoset x ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) := by
  rw [atkinLehnerAntiInvolutionGamma1_bar_eq]
  obtain ⟨A₀, hA₀, hxdet, ⟨c, hc⟩, hAunit⟩ := (mem_Delta0_iff N).mp hx
  obtain rfl : A = A₀ := Matrix.map_injective Int.cast_injective (hA.symm.trans hA₀)
  have hAco : Int.gcd (A 0 0) N = 1 := Int.isUnit_intCast_iff_gcd_eq_one.mp hAunit
  have hA_det_pos : 0 < A.det := by
    rw [← Int.cast_pos (R := ℚ), Int.cast_det, ← hA]
    exact hxdet
  obtain ⟨m, hm⟩ : ∃ m : ℕ, A.det = (m : ℤ) :=
    ⟨A.det.natAbs, (Int.natAbs_of_nonneg hA_det_pos.le).symm⟩
  have hm_pos : 0 < m := by exact_mod_cast hm ▸ hA_det_pos
  have hdet_m : (x : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ) := by
    rw [hA, ← Int.cast_det A, hm]
    norm_cast
  -- `x` and its image lie in the `Γ₀(N)` double coset of `diag(1, m)`
  have hx₀ := mem_doubleCoset_natDiagGL_of_primitive N m x A hA ⟨c, hc⟩ hAco hdet_m hprim
  have hbar₀ : (atkinLehnerAntiInvolution N).bar x hx ∈ doubleCoset (natDiagGL 2 ![1, m])
      ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) := by
    rw [← doubleCoset_eq_of_mem hx₀]
    exact atkinLehnerAntiInvolution_bar_mem_doubleCoset N x hx
  -- `σ ∈ Γ₀(N)` with upper-left entry inverse to that of `x` modulo `N`
  obtain ⟨σ, hσlabel⟩ := Gamma0Map_toHomUnits_surjective (N := N) hAunit.unit
  have hσ11 : (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = A 0 0 := by
    simpa [Gamma0Map_apply] using congrArg Units.val hσlabel
  have hσ00 : (((σ : SL(2, ℤ)) 0 0 : ℤ) : ZMod N) * (A 0 0 : ZMod N) = 1 := by
    rw [← hσ11]
    exact intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 σ.2
  have hσ₀ : mapGL ℚ (σ : SL(2, ℤ)) ∈ (Gamma0 N).map (mapGL ℚ) :=
    Subgroup.mem_map_of_mem _ σ.2
  -- left multiplication by `σ` lands both in the `Γ₁(N)` double coset of `diag(1, m)`
  have hσx := mapGL_mul_mem_doubleCoset_Gamma1_of_mem_doubleCoset_Gamma0 hm_pos hσ₀ hσ00 hA rfl
    ⟨c, hc⟩ hx₀
  have hσbar := mapGL_mul_mem_doubleCoset_Gamma1_of_mem_doubleCoset_Gamma0 hm_pos hσ₀ hσ00
    (atkinLehnerAntiInvolution_bar_val N hx A hA c hc) (by simp) ⟨A 0 1, by simp⟩ hbar₀
  rw [← doubleCoset_eq_of_mem hσx] at hσbar
  -- cancel `σ`, which normalizes `Γ₁(N)`
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, heq⟩ := mem_doubleCoset.mp hσbar
  have hnorm := Subgroup.inv_mem _ (mapGL_mem_normalizer_Gamma1_map ℚ σ)
  refine mem_doubleCoset.mpr ⟨(mapGL ℚ (σ : SL(2, ℤ)))⁻¹ * γ₁ * mapGL ℚ (σ : SL(2, ℤ)), ?_,
    γ₂, hγ₂, ?_⟩
  · simpa using (Subgroup.mem_normalizer_iff.mp hnorm γ₁).mp hγ₁
  · calc (atkinLehnerAntiInvolution N).bar x hx
        = (mapGL ℚ (σ : SL(2, ℤ)))⁻¹ *
            (mapGL ℚ (σ : SL(2, ℤ)) * (atkinLehnerAntiInvolution N).bar x hx) := by group
      _ = _ := by rw [heq]; group

/-- **The Atkin–Lehner anti-involution fixes every `Γ₁(N)` double coset in `Δ₀(N)`.** It fixes
the scalars, as at level `Γ₀(N)`, so `HeckeRing.GL2.bar_mem_doubleCoset_of_forall_primitive`
reduces to a primitive witness. -/
theorem atkinLehnerAntiInvolutionGamma1_bar_mem_doubleCoset (x : GL (Fin 2) ℚ)
    (hx : x ∈ Delta0 N) : (atkinLehnerAntiInvolutionGamma1 N).bar x hx ∈
      doubleCoset x ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) :=
  bar_mem_doubleCoset_of_forall_primitive N (atkinLehnerAntiInvolutionGamma1 N)
    (fun _ hd hs ↦ by
      rw [atkinLehnerAntiInvolutionGamma1_bar_eq]
      exact atkinLehnerAntiInvolution_bar_natDiagGL_const N hd hs)
    (atkinLehnerAntiInvolutionGamma1_bar_mem_doubleCoset_of_primitive N) x hx

/-- **The Atkin–Lehner anti-involution acts trivially on `Γ₁(N) \ Δ₀(N) / Γ₁(N)`.** -/
@[simp] lemma atkinLehnerAntiInvolutionGamma1_onHeckeCoset_eq_self
    (D : HeckeCoset (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))) :
    (atkinLehnerAntiInvolutionGamma1 N).onHeckeCoset D = D := by
  induction D using HeckeCoset.induction with
  | h g =>
    rw [(atkinLehnerAntiInvolutionGamma1 N).onHeckeCoset_mk]
    exact HeckeCoset.mk_eq_mk_of_mem
      (atkinLehnerAntiInvolutionGamma1_bar_mem_doubleCoset N (g : GL (Fin 2) ℚ) g.2)

/-- **Shimura's Proposition 3.8 for `Γ₁(N)`**: the Hecke ring `R(Γ₁(N), Δ₀(N))` over any
commutative semiring is commutative. It contains the diamond operators as well as the Hecke
operators `T(1, n)`. Not an instance, since the anti-involution is data, as for
`HeckeRing.GL2.commSemiringHeckeRingGamma0`. -/
@[instance_reducible]
noncomputable def commSemiringHeckeRingGamma1 (R : Type*) [CommSemiring R] :
    CommSemiring (𝕋 (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) R) :=
  HeckeCosetModule.commSemiringOfAntiInvolution R (atkinLehnerAntiInvolutionGamma1 N)
    (atkinLehnerAntiInvolutionGamma1_onHeckeCoset_eq_self N)

/-- The ambient automorphism `g ↦ ι(g⁻¹)` preserves the image of `Γ₁(N)`. -/
@[simp] theorem atkinLehnerAutomorphism_map_Gamma1 :
    ((Gamma1 N).map (mapGL ℚ)).map (atkinLehnerAutomorphism N :
        GL (Fin 2) ℚ →* GL (Fin 2) ℚ) = (Gamma1 N).map (mapGL ℚ) := by
  have hmem {y : GL (Fin 2) ℚ} (hy : y ∈ (Gamma1 N).map (mapGL ℚ)) :
      atkinLehnerAutomorphism N y ∈ (Gamma1 N).map (mapGL ℚ) := by
    have hy' := inv_mem hy
    have hyΔ : y⁻¹ ∈ Delta0 N := IsHeckeTriple.mem_of_mem_left (Δ := Delta0 N)
      ((Gamma1 N).map (mapGL ℚ)) hy'
    rw [← inv_inv y, atkinLehnerAutomorphism_inv_apply N hyΔ,
      ← atkinLehnerAntiInvolutionGamma1_bar_eq]
    exact (atkinLehnerAntiInvolutionGamma1 N).bar_mem_H hyΔ hy'
  ext x
  refine ⟨fun ⟨y, hy, hyx⟩ ↦ hyx ▸ hmem hy, fun hx ↦ ?_⟩
  exact ⟨atkinLehnerAutomorphism N x, hmem hx, atkinLehnerAutomorphism_involutive N x⟩

/-- **Shimura's multiplicity at level `Γ₁(N)` is symmetric at inverted arguments.** For
`δ₁, δ₂, d ∈ Δ₀(N)`, `m(δ₂⁻¹, δ₁⁻¹; d⁻¹) = m(δ₁⁻¹, δ₂⁻¹; d⁻¹)`. These are the coefficients of
the composite of two Hecke operators acting through right-coset representatives. The
automorphism `g ↦ ι(g⁻¹)` carries them to multiplicities at `ι(δ₂), ι(δ₁), ι(d) ∈ Δ₀(N)`, where
`HeckeAntiInvolution.multiplicity_comm` applies. -/
theorem multiplicity_inv_comm_Gamma1 {δ₁ δ₂ d : GL (Fin 2) ℚ} (h₁ : δ₁ ∈ Delta0 N)
    (h₂ : δ₂ ∈ Delta0 N) (hd : d ∈ Delta0 N) :
    multiplicity ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))
        ((Gamma1 N).map (mapGL ℚ)) δ₂⁻¹ δ₁⁻¹ d⁻¹ =
      multiplicity ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))
        ((Gamma1 N).map (mapGL ℚ)) δ₁⁻¹ δ₂⁻¹ d⁻¹ := by
  set ι := atkinLehnerAntiInvolutionGamma1 N
  have key (a b : GL (Fin 2) ℚ) (ha : a ∈ Delta0 N) (hb : b ∈ Delta0 N) :
      multiplicity ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))
          ((Gamma1 N).map (mapGL ℚ)) a⁻¹ b⁻¹ d⁻¹ =
        multiplicity ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))
          ((Gamma1 N).map (mapGL ℚ)) (ι.bar a ha) (ι.bar b hb) (ι.bar d hd) := by
    rw [← multiplicity_map_equiv (atkinLehnerAutomorphism N), atkinLehnerAutomorphism_map_Gamma1,
      atkinLehnerAutomorphism_inv_apply N ha, atkinLehnerAutomorphism_inv_apply N hb,
      atkinLehnerAutomorphism_inv_apply N hd, ← atkinLehnerAntiInvolutionGamma1_bar_eq,
      ← atkinLehnerAntiInvolutionGamma1_bar_eq, ← atkinLehnerAntiInvolutionGamma1_bar_eq]
  rw [key δ₂ δ₁ h₂ h₁, key δ₁ δ₂ h₁ h₂]
  exact ι.multiplicity_comm (atkinLehnerAntiInvolutionGamma1_onHeckeCoset_eq_self N)
    ⟨_, ι.bar_mem_Δ δ₂ h₂⟩ ⟨_, ι.bar_mem_Δ δ₁ h₁⟩ ⟨_, ι.bar_mem_Δ d hd⟩

end HeckeRing.GL2
