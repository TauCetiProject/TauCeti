/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Extension
public import TauCeti.Topology.VectorBundle.Pullback

/-!
# Extension of a lift of the orthonormal frame bundle commutes with pullback

Let `s` be a lift of the orthonormal frame bundle of a real vector bundle `E → X` along
`ρ : G →* GL(ℝⁿ)`, with principal `G`-bundle `P`, and let `σ : G →* H` be a continuous homomorphism
lifting `ρ` along `ρ' : H →* GL(ℝⁿ)`. For a continuous map `g : Y → X`, extending along `σ`
commutes with pulling back along `g`: `(g^* s).extend σ ≃ g^* (s.extend σ)`
(`TauCeti.OrthonormalFrameLift.extendPullbackEquiv`). Both principal bundles are, over `y ∈ Y`,
the extension `P_{g y} ×_σ H`; the equivalence is the identity `[p, h] ↦ [p, h]`, obtained from the
universal property of the extension (`TauCeti.OrthonormalFrameLift.extendEquivOfEquivariant`)
applied to `p ↦ [p, 1]`, which preserves frames
(`TauCeti.OrthonormalFrameLift.toFrame_pullback_extend_inl`).

## Main definitions

* `TauCeti.OrthonormalFrameLift.extendPullbackEquiv`: `(g^* s).extend σ ≃ g^* (s.extend σ)`.

## Main results

* `TauCeti.OrthonormalFrameLift.toFrame_pullback_extend_inl`: the frame of `[p, 1]` in
  `g^* (s.extend σ)` is the frame of `p` in `g^* s`.
* `TauCeti.OrthonormalFrameLift.extendPullbackEquiv_toEquiv_mk`,
  `TauCeti.OrthonormalFrameLift.extendPullbackEquiv_toEquiv_inl`: the equivalence sends `[p, h]`
  to `[p, h]` and `[p, 1]` to `[p, 1]`.
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
  {H : Type w} [Group H] [TopologicalSpace H]
  {ρ' : H →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)}
  {Y : Type*} [TopologicalSpace Y] {K : Type*} [FunLike K Y X] [ContinuousMapClass K Y X]
  (s : OrthonormalFrameLift F E n G ρ) (σ : G →* H) (hσ : Continuous σ) (hσρ : ρ'.comp σ = ρ)
  (hρ'n : ∀ h v, ‖WithLp.toLp 2 (ρ' h v)‖ = ‖WithLp.toLp 2 v‖)
  (hρ'c : ∀ v, Continuous fun h ↦ ρ' h v)

variable [ContinuousMul H] in
/-- **The frame of `[p, 1]`** in the pullback of the extension of a lift `s` is the frame of `p`
in the pullback of `s`. -/
@[simp]
theorem toFrame_pullback_extend_inl (g : K) (y : Y) (p : s.P (g y)) :
    ((s.extend σ hσ hσρ hρ'n hρ'c).pullback g).toFrame ⟨y, Extend.inl σ hσ p⟩ =
      (s.pullback g).toFrame ⟨y, p⟩ := by
  obtain ⟨φ, hφ⟩ := s.exists_toFrame_eq_mk ⟨g y, p⟩
  rw [(s.extend σ hσ hσρ hρ'n hρ'c).toFrame_pullback_mk g y _
    ((s.toFrame_extend_inl σ hσ hσρ hρ'n hρ'c (g y) p).trans hφ), s.toFrame_pullback_mk g y p hφ]

variable [IsTopologicalGroup H]

/-- **Extension commutes with pullback**: for a continuous map `g : Y → X`,
`(g^* s).extend σ ≃ g^* (s.extend σ)`. Over `y`, both principal bundles are `P_{g y} ×_σ H`, and
the equivalence is `[p, h] ↦ [p, h]`. -/
noncomputable def extendPullbackEquiv (g : K) :
    ((s.pullback g).extend σ hσ hσρ hρ'n hρ'c).Equiv
      ((s.extend σ hσ hσρ hρ'n hρ'c).pullback g) :=
  (s.pullback g).extendEquivOfEquivariant σ hσ hσρ hρ'n hρ'c
    ((s.extend σ hσ hσρ hρ'n hρ'c).pullback g) (fun _ (p : s.P _) ↦ Extend.inl σ hσ p)
    (fun _ (p : s.P _) h ↦ Extend.inl_smul σ hσ p h)
    (Pullback.continuous_fiberwise (Extend.continuous_inl s.P σ hσ) (g : Y → X))
    (s.toFrame_pullback_extend_inl σ hσ hσρ hρ'n hρ'c g)

/-- The equivalence `(g^* s).extend σ ≃ g^* (s.extend σ)` sends `[p, h]` to `[p, h]`. -/
theorem extendPullbackEquiv_toEquiv_mk (g : K) (y : Y) (p : s.P (g y)) (h : H) :
    (s.extendPullbackEquiv σ hσ hσρ hρ'n hρ'c g).toEquiv y
        (Extend.mk (P := (g : Y → X) *ᵖ s.P) σ hσ p h) =
      Extend.mk (P := s.P) σ hσ p h :=
  (extendEquivOfEquivariant_toEquiv_mk ..).trans (Extend.smul_inl σ hσ p h)

/-- The equivalence `(g^* s).extend σ ≃ g^* (s.extend σ)` sends `[p, 1]` to `[p, 1]`. -/
theorem extendPullbackEquiv_toEquiv_inl (g : K) (y : Y) (p : s.P (g y)) :
    (s.extendPullbackEquiv σ hσ hσρ hρ'n hρ'c g).toEquiv y
        (Extend.inl (P := (g : Y → X) *ᵖ s.P) σ hσ p) =
      Extend.inl (P := s.P) σ hσ p :=
  extendEquivOfEquivariant_toEquiv_inl ..

end OrthonormalFrameLift

end TauCeti
