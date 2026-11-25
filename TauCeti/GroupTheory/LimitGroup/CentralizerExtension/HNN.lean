/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Basic
import TauCeti.GroupTheory.HNNExtension.Map
import TauCeti.GroupTheory.Subgroup.Centralizer

/-!
# HNN extensions along centralizers mapped to an extension of a centralizer

Let `B` be a group and `α, β ∈ B`, and let `φ : C_B(α) ≃* C_B(β)` be an isomorphism of their
centralizers sending `α` to `β`. The HNN extension `HNNExtension B (C_B(α)) (C_B(β)) φ`, with
`t a t⁻¹ = φ a`, maps to an extension of a centralizer: given an embedding `θ : B →* K` and
`k ∈ K` with `θ (φ a) = k⁻¹ θ(a) k`, send `B` by `θ` and `t` to `(k s)⁻¹`, where `s` is the new
letter of `K(θ β, ℤ)` (`TauCeti.LimitGroup.CentralizerExt.hnnLift`). This homomorphism is injective
(`TauCeti.LimitGroup.CentralizerExt.hnnLift_injective`): by Britton's lemma, a reduced word of the
HNN extension goes to a reduced word of `K(θ β, ℤ)` of the same length in the new letter, since a
pinch `s⁻¹ (k⁻¹ θ(b) k) s` or `s θ(b) s⁻¹` occurs exactly when `θ(b)` commutes with `θ(α)` or with
`θ(β)`, that is, when `b` lies in an associated subgroup.

This gives each conjugate atom `z⁻¹ c z` of a standard quadratic equation its own letter of an
extension of a centralizer, as in the pinch argument of [VAR-I], Propositions 10–14. There the
associated subgroups are the cyclic groups `⟨c⟩`; here they are the full centralizers, which is
what makes the pinches of the HNN extension and of the extension of a centralizer correspond.

## Main definitions

* `TauCeti.LimitGroup.CentralizerExt.hnnLift`: the homomorphism
  `HNNExtension B (C_B(α)) (C_B(β)) φ →* K(θ β, ℤ)`.

## Main results

* `TauCeti.LimitGroup.CentralizerExt.hnnLift_injective`: it is injective.

## Implementation notes

Conjugation by `k⁻¹` maps `C_K(θ α)` onto `C_K(θ β)`. The homomorphism `K(θ β, ℤ)` to the HNN
extension of `K` along it that is the identity on `K` and sends `s` to `k⁻¹ t⁻¹`, composed with
`hnnLift`, is the homomorphism of HNN extensions induced by `θ`. That one is injective by the
Britton transfer `HNNExtension.map_injective`, since `θ` pulls `C_K(θ α)` and `C_K(θ β)` back to
`C_B(α)` and `C_B(β)`; hence so is `hnnLift`.

## References

* R. C. Lyndon, P. E. Schupp, *Combinatorial group theory*, Springer (1977), Chapter IV, §2
  (Britton's lemma).
* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §5,
  Propositions 10–14.
-/

public section

open Subgroup

namespace TauCeti.LimitGroup.CentralizerExt

variable {B K : Type*} [Group B] [Group K] {α β : B}

/-- The homomorphism `HNNExtension B (C_B(α)) (C_B(β)) φ →* K(θ β, ℤ)` that is `θ` on `B` and
sends the stable letter `t` to `(k s)⁻¹`, where `s = t 0` is the new letter of `K(θ β, ℤ)`. It is
well defined when `θ (φ a) = k⁻¹ θ(a) k` for `a ∈ C_B(α)`. -/
def hnnLift (φ : centralizer {α} ≃* centralizer {β}) (θ : B →* K) (k : K)
    (hφ : ∀ a : centralizer {α}, θ (φ a) = k⁻¹ * θ a * k) :
    HNNExtension B (centralizer {α}) (centralizer {β}) φ →* CentralizerExt (θ β) 1 :=
  HNNExtension.lift (of.comp θ) (of k * t 0)⁻¹ fun a ↦ by
    -- `θ (φ a)` centralizes `θ β`, so it commutes with the new letter.
    have hβ : θ (φ a) ∈ centralizer {θ β} := by
      simpa using (θ.centralizerMap Set.image_singleton.superset (φ a)).property
    have hc := (commute_of_t (n := 1) hβ 0).inv_right
    simp only [MonoidHom.comp_apply, mul_inv_rev, mul_assoc]
    rw [← mul_assoc (of (θ _)), hc.eq, hφ]
    simp [mul_assoc]

@[simp] theorem hnnLift_of (φ : centralizer {α} ≃* centralizer {β}) (θ : B →* K) (k : K)
    (hφ : ∀ a : centralizer {α}, θ (φ a) = k⁻¹ * θ a * k) (b : B) :
    hnnLift φ θ k hφ (HNNExtension.of b) = of (θ b) :=
  HNNExtension.lift_of _ _ _ b

@[simp] theorem hnnLift_t (φ : centralizer {α} ≃* centralizer {β}) (θ : B →* K) (k : K)
    (hφ : ∀ a : centralizer {α}, θ (φ a) = k⁻¹ * θ a * k) :
    hnnLift φ θ k hφ HNNExtension.t = (of k * t 0)⁻¹ :=
  HNNExtension.lift_t _ _ _

/-- **Britton transfer.** If `θ : B →* K` is injective and `φ : C_B(α) ≃* C_B(β)` sends `α` to
`β` and is conjugation by `k` after `θ`, the homomorphism
`HNNExtension B (C_B(α)) (C_B(β)) φ →* K(θ β, ℤ)` that is `θ` on `B` and sends `t` to `(k s)⁻¹`
is injective. -/
theorem hnnLift_injective (φ : centralizer {α} ≃* centralizer {β})
    (hφβ : (φ ⟨α, mem_centralizer_singleton_iff.2 rfl⟩ : B) = β) {θ : B →* K}
    (hθ : Function.Injective θ) {k : K} (hφ : ∀ a : centralizer {α}, θ (φ a) = k⁻¹ * θ a * k) :
    Function.Injective (hnnLift φ θ k hφ) := by
  -- `θ β = k⁻¹ θ(α) k`, so conjugation by `k⁻¹` maps `C_K(θ α)` onto `C_K(θ β)`.
  have hαβ : θ β = k⁻¹ * θ α * k := hφβ ▸ hφ ⟨α, mem_centralizer_singleton_iff.2 rfl⟩
  let ψ : centralizer {θ α} ≃* centralizer {θ β} :=
    MulEquiv.centralizerMap (MulAut.conj k⁻¹) (by simp [hαβ])
  -- `θ` pulls the centralizer of `θ x` back to the centralizer of `x`.
  have hC (x : B) : (centralizer {θ x}).comap θ = centralizer {x} := by
    simpa using comap_centralizer_image_of_injective hθ {x}
  -- `K(θ β, ℤ)` maps to the HNN extension of `K` along `ψ` by `s ↦ k⁻¹ t⁻¹`; after `hnnLift`, this
  -- is the homomorphism of HNN extensions induced by `θ`, which is injective.
  let Ψ : CentralizerExt (θ β) 1 →* HNNExtension K _ _ ψ :=
    lift HNNExtension.of (fun _ ↦ HNNExtension.of k⁻¹ * HNNExtension.t⁻¹)
      (fun _ _ ↦ .refl _) fun c hc _ ↦ by
        have h : HNNExtension.t⁻¹ * HNNExtension.of c =
            (HNNExtension.of (k * c * k⁻¹) * HNNExtension.t⁻¹ : HNNExtension K _ _ ψ) := by
          simpa [ψ] using HNNExtension.inv_t_mul_of (φ := ψ) ⟨c, hc⟩
        simp [Commute, SemiconjBy, mul_assoc, h]
  have hΨ : Ψ.comp (hnnLift φ θ k hφ) = HNNExtension.map θ (hC α).ge fun a ↦ by simp [ψ, hφ] :=
    HNNExtension.hom_ext (by ext; simp [Ψ]) (by simp [Ψ])
  refine Function.Injective.of_comp (f := Ψ) ?_
  rw [← MonoidHom.coe_comp, hΨ]
  exact HNNExtension.map_injective hθ (hC α).le (hC β).le

/-! ### Over the free group of rank two -/

/-- Over `F(a, b)`, conjugation by `b` maps `C(a)` onto `C(b a b⁻¹)`, and the HNN extension of
`F(a, b)` along it embeds in `F(a, b)(b a b⁻¹, ℤ)`, with `θ` the identity and `k = b⁻¹`. -/
example : Function.Injective (hnnLift
    (MulEquiv.centralizerMap (MulAut.conj (FreeGroup.of 1)) (by simp) :
      centralizer {FreeGroup.of (0 : Fin 2)} ≃*
        centralizer {FreeGroup.of 1 * FreeGroup.of (0 : Fin 2) * (FreeGroup.of 1)⁻¹})
    (.id _) (FreeGroup.of 1)⁻¹ fun _ ↦ by simp) :=
  hnnLift_injective _ (by simp) Function.injective_id _

end TauCeti.LimitGroup.CentralizerExt
