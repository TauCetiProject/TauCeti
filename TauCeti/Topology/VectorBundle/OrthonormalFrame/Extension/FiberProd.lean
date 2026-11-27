/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Extension
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.FiberProd

/-!
# Extension of a lift of the orthonormal frame bundle commutes with fibre products

Let `s` be a lift of the orthonormal frame bundle of a real vector bundle `E → X` along
`ρ : G →* GL(ℝⁿ)`, with principal `G`-bundle `P`, let `σ : G →* K` be a continuous homomorphism
lifting `ρ` along `ρ' : K →* GL(ℝⁿ)`, and let `Q` be a principal `H`-bundle over `X`. Extending
the fibre product `s ×_X Q` along `σ × id : G × H →* K × H` is the fibre product of the extension
`s.extend σ` with `Q` (`TauCeti.OrthonormalFrameLift.extendFiberProdEquiv`): over `x`, the class
`[(p, q), (k, h)]` corresponds to `([p, k], q • h)`. The equivalence is obtained from the
universal property of the extension (`TauCeti.OrthonormalFrameLift.extendEquivOfEquivariant`)
applied to `(p, q) ↦ ([p, 1], q)`.

Combined with `TauCeti.OrthonormalFrameLift.extendCompEquiv`, this rewrites an iterated
construction such as `((s ×_X Q).extend μ ×_X Q).extend μ` as a single extension of
`(s ×_X Q) ×_X Q`; the twist of a Spin structure by a principal `ℤ/2`-bundle is undone by a
second twist by the same bundle in this way (`TauCeti.SpinStructure.twistTwistEquiv`).

## Main definitions

* `TauCeti.OrthonormalFrameLift.extendFiberProdEquiv`:
  `(s ×_X Q).extend (σ × id) ≃ (s.extend σ) ×_X Q`.

## Main results

* `TauCeti.OrthonormalFrameLift.extendFiberProdEquiv_toEquiv_mk`,
  `TauCeti.OrthonormalFrameLift.extendFiberProdEquiv_toEquiv_inl`: the equivalence sends
  `[(p, q), (k, h)]` to `([p, k], q • h)` and `[(p, q), 1]` to `([p, 1], q)`.
-/

public section

open Bundle MulOpposite TauCeti.PrincipalBundle

universe w

namespace TauCeti

namespace OrthonormalFrameLift

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : X → Type w} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E] {n : ℕ}
  {G : Type*} [Group G] [TopologicalSpace G] {ρ : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)}
  {K : Type w} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  {ρ' : K →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)}
  {H : Type w} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (Q : X → Type w) [TopologicalSpace (TotalSpace H Q)] [∀ x, TopologicalSpace (Q x)]
  [FiberBundle H Q] [∀ x, MulAction Hᵐᵒᵖ (Q x)] [PrincipalBundle H Q]
  (s : OrthonormalFrameLift F E n G ρ) (σ : G →* K) (hσ : Continuous σ) (hσρ : ρ'.comp σ = ρ)
  (hρ'n : ∀ k v, ‖WithLp.toLp 2 (ρ' k v)‖ = ‖WithLp.toLp 2 v‖)
  (hρ'c : ∀ v, Continuous fun k ↦ ρ' k v)

/-- **Extension commutes with fibre products**: the extension of the fibre product `s ×_X Q` along
`σ × id : G × H →* K × H` is equivalent to the fibre product of the extension `s.extend σ` with
`Q`. Over `x`, the class `[(p, q), (k, h)]` is sent to `([p, k], q • h)`. -/
noncomputable def extendFiberProdEquiv :
    ((s.fiberProd H Q).extend (ρ' := ρ'.comp (MonoidHom.fst K H)) (σ.prodMap (MonoidHom.id H))
        (hσ.prodMap continuous_id) (MonoidHom.ext fun _ ↦ by rw [← hσρ]; rfl)
        (fun k v ↦ hρ'n k.1 v)
        (fun v ↦ (hρ'c v).comp continuous_fst)).Equiv
      ((s.extend σ hσ hσρ hρ'n hρ'c).fiberProd H Q) :=
  (s.fiberProd H Q).extendEquivOfEquivariant _ _ _ _ _ _
    (fun _ z ↦ FiberProd.mk (Extend.inl σ hσ (FiberProd.fst (P := s.P) (Q := Q) z))
      (FiberProd.snd (P := s.P) (Q := Q) z))
    (fun _ z g ↦ congrArg (fun e ↦ FiberProd.mk (P := Extend s.P σ hσ) (Q := Q) e
      (op g.2 • FiberProd.snd (P := s.P) (Q := Q) z)) (Extend.inl_smul σ hσ _ g.1))
    (((Extend.continuous_inl s.P σ hσ).comp
      FiberProd.continuous_totalSpaceMk_fst).totalSpaceMk_fiberProdMk
        FiberProd.continuous_totalSpaceMk_snd)
    (fun x _ ↦ s.toFrame_extend_inl σ hσ hσρ hρ'n hρ'c x _)

/-- The equivalence `(s ×_X Q).extend (σ × id) ≃ (s.extend σ) ×_X Q` sends `[(p, q), (k, h)]` to
`([p, k], q • h)`. -/
@[simp]
theorem extendFiberProdEquiv_toEquiv_mk (x : X) (p : s.P x) (q : Q x) (k : K) (h : H) :
    (s.extendFiberProdEquiv Q σ hσ hσρ hρ'n hρ'c).toEquiv x
        (Extend.mk (σ.prodMap (MonoidHom.id H)) (hσ.prodMap continuous_id)
          (P := FiberProd s.P Q) (FiberProd.mk p q) (k, h)) =
      FiberProd.mk (Extend.mk σ hσ p k) (op h • q) :=
  (extendEquivOfEquivariant_toEquiv_mk ..).trans
    (congrArg (FiberProd.mk (P := Extend s.P σ hσ) (Q := Q) · (op h • q))
      (Extend.smul_inl σ hσ p k))

/-- The equivalence `(s ×_X Q).extend (σ × id) ≃ (s.extend σ) ×_X Q` sends `[(p, q), 1]` to
`([p, 1], q)`. -/
@[simp]
theorem extendFiberProdEquiv_toEquiv_inl (x : X) (p : s.P x) (q : Q x) :
    (s.extendFiberProdEquiv Q σ hσ hσρ hρ'n hρ'c).toEquiv x
        (Extend.inl (σ.prodMap (MonoidHom.id H)) (hσ.prodMap continuous_id)
          (P := FiberProd s.P Q) (FiberProd.mk p q)) =
      FiberProd.mk (Extend.inl σ hσ p) q :=
  extendEquivOfEquivariant_toEquiv_inl ..

end OrthonormalFrameLift

end TauCeti
