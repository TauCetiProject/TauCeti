/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Topology.FiberBundle.Principal.Extension
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Lift.Basic

/-!
# Extending a lift of the orthonormal frame bundle along a structure group homomorphism

Let `s` be a lift of the orthonormal frame bundle of a real vector bundle `E` along
`ρ : G →* GL(ℝⁿ)` (`TauCeti.OrthonormalFrameLift`), with principal `G`-bundle `P`. Let
`σ : G →* H` be a continuous homomorphism and `ρ' : H →* GL(ℝⁿ)` a homomorphism by Euclidean
isometries, continuous in the sense that `h ↦ ρ' h v` is continuous for every `v`, with
`ρ' ∘ σ = ρ`. The **extension** `s.extend σ hσ ρ' …` is the lift along `ρ'` whose principal
`H`-bundle is the extension of structure group `P ×_σ H` (`TauCeti.PrincipalBundle.Extend`) and
whose frame map sends `[p, h]` to the frame of `p` composed with `ρ' h`. It is characterized by
`TauCeti.OrthonormalFrameLift.toFrame_extend_inl`: the frame of `[p, 1]` is the frame of `p`.

This is how a lift is induced from a reduction of the structure group. The canonical `Spinᶜ`
structure of an almost Hermitian four-manifold is the extension of its unitary frame bundle, a
lift along `U(2) ⊆ SO(4)`, along the canonical homomorphism `U(2) → Spinᶜ(4)`
(`TauCeti.SeibergWitten.unitaryLift`); the Spin structure and the `Spinᶜ` structure it induces are
related by the homomorphism `Spin(n) → Spinᶜ(n)` in the same way.

The extension has the universal property of the extension of structure group
(`TauCeti.OrthonormalFrameLift.extendEquivOfEquivariant`): a lift `t` along `ρ'` receiving a
continuous `σ`-equivariant map from `P` that preserves frames is equivalent to `s.extend …`. As
consequences, equivalences of lifts extend to equivalences of the extensions
(`TauCeti.OrthonormalFrameLift.Equiv.extend`), and extending along `σ` and then along `τ` is
extending along `τ ∘ σ` (`TauCeti.OrthonormalFrameLift.extendCompEquiv`).

## Main definitions

* `TauCeti.OrthonormalFrameLift.extend`: the extension of a lift along a structure group
  homomorphism.
* `TauCeti.OrthonormalFrameLift.extendEquivOfEquivariant`: the equivalence of the extension with
  any lift receiving an equivariant frame-preserving map.

## Main results

* `TauCeti.OrthonormalFrameLift.toFrame_extend_inl` and
  `TauCeti.OrthonormalFrameLift.frameAt_extend_inl`: the frame of `[p, 1]` is the frame of `p`.
* `TauCeti.OrthonormalFrameLift.toFrame_extend_mk`: the frame of `[p, h]` is the frame of `p`
  composed with `ρ' h`.

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter I, §5 (reductions and extensions of the structure group).
* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D
  (the `Spinᶜ` structure induced by a `U(n)` reduction).
-/

public section

open Bundle MulOpposite TauCeti.PrincipalBundle

universe w

namespace TauCeti

namespace OrthonormalFrameLift

variable {X : Type*} [TopologicalSpace X] {F : Type*} {E : X → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] {n : ℕ}
  {G : Type*} [Group G] [TopologicalSpace G] {ρ : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)}
  {H : Type w} [Group H] [TopologicalSpace H] {ρ' : H →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)}

section Construction

variable [ContinuousMul H]

variable (s : OrthonormalFrameLift F E n G ρ) (σ : G →* H) (hσ : Continuous σ)
  (hσρ : ρ'.comp σ = ρ) (hρ'n : ∀ h v, ‖WithLp.toLp 2 (ρ' h v)‖ = ‖WithLp.toLp 2 v‖)
  (hρ'c : ∀ v, Continuous fun h ↦ ρ' h v)

/-- The map to frames of the extension of a lift (`TauCeti.OrthonormalFrameLift.extend`): the
class `[p₀, h]`, for the reference point `p₀` of the fibre of `P`, is sent to the frame of `p₀`
composed with `ρ' h`. Every class `[p, h]` is sent to the frame of `p` composed with `ρ' h`
(`TauCeti.OrthonormalFrameLift.toFrame_extend_mk`). -/
noncomputable def extendToFrame (z : TotalSpace H (Extend s.P σ hσ)) :
    OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin n)) :=
  let p₀ : s.P z.proj := (FiberBundle.homeomorphAt G s.P z.proj).symm 1
  ⟨(s.toFrame ⟨z.proj, p₀⟩).proj,
    ((ρ' (division H (Extend.inl σ hσ p₀) z.snd)).toEuclideanIsometry (hρ'n _)).trans
      (s.toFrame ⟨z.proj, p₀⟩).frame⟩

/-- The map to frames of the extension covers the identity of the base. -/
@[simp]
theorem proj_extendToFrame (z : TotalSpace H (Extend s.P σ hσ)) :
    (s.extendToFrame σ hσ hρ'n z).proj = z.proj :=
  s.proj_toFrame _

/-- Unfolds the frame map of the extension at the vector `v`. -/
private theorem totalSpaceMk_extendToFrame (x : X) (z : Extend s.P σ hσ x) (v : Fin n → ℝ) :
    TotalSpace.mk' F (extendToFrame s σ hσ hρ'n ⟨x, z⟩).proj
        ((extendToFrame s σ hσ hρ'n ⟨x, z⟩).frame (WithLp.toLp 2 v)) =
      TotalSpace.mk' F (s.toFrame ⟨x, (FiberBundle.homeomorphAt G s.P x).symm 1⟩).proj
        ((s.toFrame ⟨x, (FiberBundle.homeomorphAt G s.P x).symm 1⟩).frame
          (WithLp.toLp 2
            (ρ' (division H (Extend.inl σ hσ ((FiberBundle.homeomorphAt G s.P x).symm 1)) z)
              v))) := by
  rw [extendToFrame, LinearIsometryEquiv.trans_apply, LinearEquiv.toEuclideanIsometry_toLp]

include hσρ in
/-- The frame map of the extension sends `[p, h]` to the frame of `p` composed with `ρ' h`. -/
private theorem extendToFrame_mk (x : X) (p : s.P x) (h : H) (v : Fin n → ℝ) :
    TotalSpace.mk' F (extendToFrame s σ hσ hρ'n ⟨x, Extend.mk σ hσ p h⟩).proj
        ((extendToFrame s σ hσ hρ'n ⟨x, Extend.mk σ hσ p h⟩).frame (WithLp.toLp 2 v)) =
      TotalSpace.mk' F (s.toFrame ⟨x, p⟩).proj
        ((s.toFrame ⟨x, p⟩).frame (WithLp.toLp 2 (ρ' h v))) := by
  set p₀ : s.P x := (FiberBundle.homeomorphAt G s.P x).symm 1
  have hdiv : division H (Extend.inl σ hσ p₀) (Extend.mk σ hσ p h) =
      σ (division G p₀ p) * h := by
    rw [Extend.inl_def, Extend.division_mk, inv_one, one_mul]
  have hp : p = op (division G p₀ p) • p₀ := (smul_division p₀ p).symm
  have key := s.toFrame_smul x p₀ (division G p₀ p) (ρ' h v)
  rw [← hp, ← DFunLike.congr_fun hσρ, MonoidHom.comp_apply] at key
  rw [totalSpaceMk_extendToFrame, hdiv, map_mul, mul_apply_eq_comp]
  exact key.symm

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F E] [VectorBundle ℝ F E]

include hσρ hρ'c in
/-- The map to frames of the extension of a lift is continuous. -/
theorem continuous_extendToFrame : Continuous (extendToFrame s σ hσ hρ'n) := by
  rw [(Extend.isOpenQuotientMap_totalSpaceMk_mk s.P σ hσ).isQuotientMap.continuous_iff,
    OrthonormalFrameBundle.continuous_iff]
  intro w
  have hw : Continuous fun q : TotalSpace G s.P × H ↦
      TotalSpace.mk' F (s.toFrame q.1).proj
        ((s.toFrame q.1).frame (WithLp.toLp 2 (ρ' q.2 (WithLp.ofLp w)))) :=
    OrthonormalFrameBundle.continuous_totalSpaceMk_frame_apply.comp
      ((s.continuous_toFrame.comp continuous_fst).prodMk
        ((PiLp.continuous_toLp 2 _).comp ((hρ'c (WithLp.ofLp w)).comp continuous_snd)))
  refine hw.congr fun q ↦ ?_
  simpa using (extendToFrame_mk s σ hσ hσρ hρ'n q.1.proj q.1.snd q.2 (WithLp.ofLp w)).symm

/-- The **extension of a lift** `s` of the orthonormal frame bundle along `ρ` to a lift along
`ρ'`, through a continuous homomorphism `σ : G →* H` with `ρ' ∘ σ = ρ`, where `ρ'` acts by
Euclidean isometries, continuously in the group variable. Its principal bundle is the extension of
structure group `P ×_σ H` of the principal bundle `P` of `s`, and the frame of `[p, h]` is the frame
of `p` composed with `ρ' h` (`TauCeti.OrthonormalFrameLift.toFrame_extend_mk`). Its body is exposed
so that the fibre `(s.extend …).P x` unfolds to `Extend s.P σ hσ x` downstream. -/
@[expose]
noncomputable def extend : OrthonormalFrameLift F E n H ρ' where
  P := Extend s.P σ hσ
  toFrame := extendToFrame s σ hσ hρ'n
  continuous_toFrame := continuous_extendToFrame s σ hσ hσρ hρ'n hρ'c
  proj_toFrame := s.proj_extendToFrame σ hσ hρ'n
  toFrame_smul x z h v := by
    obtain ⟨p, h₀, rfl⟩ := Extend.exists_mk z
    rw [Extend.smul_mk, extendToFrame_mk s σ hσ hσρ, extendToFrame_mk s σ hσ hσρ, map_mul,
      mul_apply_eq_comp]

/-- The principal bundle of the extension is the extension of structure group of the principal
bundle of the lift. -/
@[simp]
theorem extend_P : (s.extend σ hσ hσρ hρ'n hρ'c).P = Extend s.P σ hσ :=
  (rfl)

/-- **The frame of `[p, h]`** in the extension of a lift is the frame of `p` composed with
`ρ' h`. -/
theorem toFrame_extend_mk (x : X) (p : s.P x) (h : H) (v : Fin n → ℝ) :
    TotalSpace.mk' F ((s.extend σ hσ hσρ hρ'n hρ'c).toFrame ⟨x, Extend.mk σ hσ p h⟩).proj
        (((s.extend σ hσ hσρ hρ'n hρ'c).toFrame ⟨x, Extend.mk σ hσ p h⟩).frame
          (WithLp.toLp 2 v)) =
      TotalSpace.mk' F (s.toFrame ⟨x, p⟩).proj
        ((s.toFrame ⟨x, p⟩).frame (WithLp.toLp 2 (ρ' h v))) :=
  extendToFrame_mk s σ hσ hσρ hρ'n x p h v

/-- **The frame of `[p, 1]`** in the extension of a lift is the frame of `p`. -/
@[simp]
theorem toFrame_extend_inl (x : X) (p : s.P x) :
    (s.extend σ hσ hσρ hρ'n hρ'c).toFrame ⟨x, Extend.inl σ hσ p⟩ = s.toFrame ⟨x, p⟩ :=
  OrthonormalFrameBundle.ext_totalSpaceMk fun v ↦ by
    rw [Extend.inl_def, toFrame_extend_mk, map_one, FunLike.coe_one_eq_id, id_eq]

/-- **The frame of `E x` at `[p, 1]`** in the extension of a lift is the frame at `p`. -/
@[simp]
theorem frameAt_extend_inl {x : X} (p : s.P x) :
    (s.extend σ hσ hσρ hρ'n hρ'c).frameAt (Extend.inl σ hσ p) = s.frameAt p := by
  have h := ((s.extend σ hσ hσρ hρ'n hρ'c).toFrame_mk (Extend.inl σ hσ p)).symm.trans
    ((s.toFrame_extend_inl σ hσ hσρ hρ'n hρ'c x p).trans (s.toFrame_mk p))
  exact OrthonormalFrameBundle.mk_eq_mk_iff.1 h

end Construction

/-! ### The universal property -/

section Universal

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsTopologicalGroup H] (s : OrthonormalFrameLift F E n G ρ) (σ : G →* H)
  (hσ : Continuous σ) (hσρ : ρ'.comp σ = ρ)
  (hρ'n : ∀ h v, ‖WithLp.toLp 2 (ρ' h v)‖ = ‖WithLp.toLp 2 v‖)
  (hρ'c : ∀ v, Continuous fun h ↦ ρ' h v)

/-- **Universal property of the extension of a lift.** A lift `t` along `ρ'` receiving a
continuous `σ`-equivariant fibrewise map `φ` from the principal bundle of `s` that preserves frames
is equivalent to the extension of `s` along `σ`, by `[p, h] ↦ φ p • h`. -/
noncomputable def extendEquivOfEquivariant (t : OrthonormalFrameLift F E n H ρ')
    (φ : ∀ x, s.P x → t.P x) (hφ : ∀ x (p : s.P x) (g : G), φ x (op g • p) = op (σ g) • φ x p)
    (hφc : Continuous fun p : TotalSpace G s.P ↦ (⟨p.proj, φ p.proj p.snd⟩ : TotalSpace H t.P))
    (hφf : ∀ x (p : s.P x), t.toFrame ⟨x, φ x p⟩ = s.toFrame ⟨x, p⟩) :
    (s.extend σ hσ hσρ hρ'n hρ'c).Equiv t where
  toEquiv := Extend.equivOfEquivariant σ hσ φ hφ
  continuous_toFun := (Extend.homeomorphOfEquivariant σ hσ φ hφ hφc).continuous.congr
    (Extend.homeomorphOfEquivariant_apply σ hσ φ hφ hφc)
  continuous_invFun := (Extend.homeomorphOfEquivariant σ hσ φ hφ hφc).symm.continuous.congr
    (Extend.homeomorphOfEquivariant_symm_apply σ hσ φ hφ hφc)
  map_smul x z h := Extend.equivOfEquivariant_smul σ hσ φ hφ x h z
  toFrame_map x z := by
    obtain ⟨p, h, rfl⟩ := Extend.exists_mk (P := s.P) (ρ := σ) (hρ := hσ) (b := x) z
    refine OrthonormalFrameBundle.ext_totalSpaceMk fun v ↦ ?_
    have ht := t.toFrame_smul x (φ x p) h v
    rw [hφf] at ht
    -- `rw` cannot see through the fibre `(s.extend …).P x = Extend s.P σ hσ x`, so the value of
    -- the comparison map at `[p, h]` is substituted by `congrArg`.
    exact (congrArg (fun q : t.P x ↦ TotalSpace.mk' F (t.toFrame ⟨x, q⟩).proj
      ((t.toFrame ⟨x, q⟩).frame (WithLp.toLp 2 v)))
        (Extend.equivOfEquivariant_mk σ hσ φ hφ p h)).trans
      (ht.trans (s.toFrame_extend_mk σ hσ hσρ hρ'n hρ'c x p h v).symm)

@[simp]
theorem extendEquivOfEquivariant_toEquiv_mk (t : OrthonormalFrameLift F E n H ρ')
    (φ : ∀ x, s.P x → t.P x) (hφ : ∀ x (p : s.P x) (g : G), φ x (op g • p) = op (σ g) • φ x p)
    (hφc : Continuous fun p : TotalSpace G s.P ↦ (⟨p.proj, φ p.proj p.snd⟩ : TotalSpace H t.P))
    (hφf : ∀ x (p : s.P x), t.toFrame ⟨x, φ x p⟩ = s.toFrame ⟨x, p⟩) (x : X) (p : s.P x)
    (h : H) :
    (s.extendEquivOfEquivariant σ hσ hσρ hρ'n hρ'c t φ hφ hφc hφf).toEquiv x
        (Extend.mk σ hσ p h) = op h • φ x p :=
  Extend.equivOfEquivariant_mk σ hσ φ hφ p h

@[simp]
theorem extendEquivOfEquivariant_toEquiv_inl (t : OrthonormalFrameLift F E n H ρ')
    (φ : ∀ x, s.P x → t.P x) (hφ : ∀ x (p : s.P x) (g : G), φ x (op g • p) = op (σ g) • φ x p)
    (hφc : Continuous fun p : TotalSpace G s.P ↦ (⟨p.proj, φ p.proj p.snd⟩ : TotalSpace H t.P))
    (hφf : ∀ x (p : s.P x), t.toFrame ⟨x, φ x p⟩ = s.toFrame ⟨x, p⟩) (x : X) (p : s.P x) :
    (s.extendEquivOfEquivariant σ hσ hσρ hρ'n hρ'c t φ hφ hφc hφf).toEquiv x
        (Extend.inl σ hσ p) = φ x p :=
  Extend.equivOfEquivariant_inl σ hσ φ hφ p

/-- **Equivalences of lifts extend**: an equivalence `s ≃ t` of lifts along `ρ` induces an
equivalence of their extensions along `σ`, sending `[p, h]` to `[φ p, h]`. -/
noncomputable def Equiv.extend {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t) :
    (s.extend σ hσ hσρ hρ'n hρ'c).Equiv (t.extend σ hσ hσρ hρ'n hρ'c) :=
  s.extendEquivOfEquivariant σ hσ hσρ hρ'n hρ'c (t.extend σ hσ hσρ hρ'n hρ'c)
    (fun x p ↦ Extend.inl σ hσ (φ.toEquiv x p))
    (fun x p g ↦ by rw [φ.map_smul]; exact Extend.inl_smul σ hσ _ g)
    ((Extend.continuous_inl t.P σ hσ).comp φ.continuous_toFun)
    (fun x p ↦ by rw [toFrame_extend_inl, φ.toFrame_map])

@[simp]
theorem Equiv.extend_toEquiv_mk {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t) (x : X)
    (p : s.P x) (h : H) :
    (φ.extend σ hσ hσρ hρ'n hρ'c).toEquiv x (Extend.mk σ hσ p h) =
      Extend.mk σ hσ (φ.toEquiv x p) h :=
  (s.extendEquivOfEquivariant_toEquiv_mk σ hσ hσρ hρ'n hρ'c _ _ _ _ _ x p h).trans
    (Extend.smul_inl σ hσ _ h)

@[simp]
theorem Equiv.extend_toEquiv_inl {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t) (x : X)
    (p : s.P x) :
    (φ.extend σ hσ hσρ hρ'n hρ'c).toEquiv x (Extend.inl σ hσ p) =
      Extend.inl σ hσ (φ.toEquiv x p) :=
  s.extendEquivOfEquivariant_toEquiv_inl σ hσ hσρ hρ'n hρ'c _ _ _ _ _ x p

/-- Extending the identity equivalence of a lift gives the identity equivalence. -/
@[simp]
theorem Equiv.extend_refl (s : OrthonormalFrameLift F E n G ρ) :
    (refl s).extend σ hσ hσρ hρ'n hρ'c = refl (s.extend σ hσ hσρ hρ'n hρ'c) := by
  ext x z
  obtain ⟨p, h, hz⟩ := Extend.exists_mk (P := s.P) (ρ := σ) (hρ := hσ) (b := x) z
  rw [← hz, extend_toEquiv_mk, refl_toEquiv, refl_toEquiv]
  rfl

/-- Extending the inverse of an equivalence of lifts gives the inverse of its extension. -/
@[simp]
theorem Equiv.extend_symm {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t) :
    φ.symm.extend σ hσ hσρ hρ'n hρ'c = (φ.extend σ hσ hσρ hρ'n hρ'c).symm := by
  ext x z
  obtain ⟨p, h, hz⟩ := Extend.exists_mk (P := t.P) (ρ := σ) (hρ := hσ) (b := x) z
  rw [← hz, symm_toEquiv]
  refine (_root_.Equiv.eq_symm_apply _).2 ?_
  rw [extend_toEquiv_mk, extend_toEquiv_mk, symm_toEquiv, _root_.Equiv.apply_symm_apply]

/-- Extending a composite of equivalences of lifts gives the composite of their extensions. -/
@[simp]
theorem Equiv.extend_trans {s t u : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    (ψ : t.Equiv u) :
    (φ.trans ψ).extend σ hσ hσρ hρ'n hρ'c =
      (φ.extend σ hσ hσρ hρ'n hρ'c).trans (ψ.extend σ hσ hσρ hρ'n hρ'c) := by
  ext x z
  obtain ⟨p, h, hz⟩ := Extend.exists_mk (P := s.P) (ρ := σ) (hρ := hσ) (b := x) z
  rw [← hz, trans_toEquiv, extend_toEquiv_mk, trans_toEquiv]
  exact ((congrArg ((ψ.extend σ hσ hσρ hρ'n hρ'c).toEquiv x)
    (extend_toEquiv_mk _ _ _ _ _ φ x p h)).trans (extend_toEquiv_mk _ _ _ _ _ ψ x _ h)).symm

end Universal

/-! ### Composition -/

section Comp

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousMul H] {K : Type w} [Group K] [TopologicalSpace K] [ContinuousMul K]
  {ρ'' : K →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)} (s : OrthonormalFrameLift F E n G ρ) (σ : G →* H)
  (hσ : Continuous σ) (hσρ : ρ'.comp σ = ρ)
  (hρ'n : ∀ h v, ‖WithLp.toLp 2 (ρ' h v)‖ = ‖WithLp.toLp 2 v‖)
  (hρ'c : ∀ v, Continuous fun h ↦ ρ' h v) (τ : H →* K) (hτ : Continuous τ)
  (hτρ : ρ''.comp τ = ρ') (hρ''n : ∀ k v, ‖WithLp.toLp 2 (ρ'' k v)‖ = ‖WithLp.toLp 2 v‖)
  (hρ''c : ∀ v, Continuous fun k ↦ ρ'' k v)

/-- **Extending along `σ` and then along `τ` is extending along `τ ∘ σ`**: the extension along
`τ ∘ σ` is equivalent to the extension along `τ` of the extension along `σ`, by
`[p, k] ↦ [[p, 1], k]`. On principal bundles this is the inverse of
`TauCeti.PrincipalBundle.Extend.compEquiv`, so its values are given by
`TauCeti.PrincipalBundle.Extend.compEquiv_symm_mk` and `compEquiv_symm_inl`. -/
noncomputable def extendCompEquiv :
    (s.extend (τ.comp σ) (hτ.comp hσ) (by rw [← MonoidHom.comp_assoc, hτρ, hσρ]) hρ''n
        hρ''c).Equiv
      ((s.extend σ hσ hσρ hρ'n hρ'c).extend τ hτ hτρ hρ''n hρ''c) where
  toEquiv x := (Extend.compEquiv σ hσ τ hτ x).symm
  continuous_toFun := (Extend.compHomeomorph σ hσ τ hτ).symm.continuous.congr
    (Extend.compHomeomorph_symm_apply σ hσ τ hτ)
  continuous_invFun := (Extend.compHomeomorph σ hσ τ hτ).continuous.congr
    (Extend.compHomeomorph_apply σ hσ τ hτ)
  map_smul x z k := Extend.compEquiv_symm_smul σ hσ τ hτ x k z
  toFrame_map x z := by
    obtain ⟨p, k, rfl⟩ := Extend.exists_mk (P := s.P) (ρ := τ.comp σ) (hρ := hτ.comp hσ) (b := x) z
    refine OrthonormalFrameBundle.ext_totalSpaceMk fun v ↦ ?_
    -- `rw` cannot see through the fibre `(s.extend …).P x = Extend s.P (τ.comp σ) _ x`, so the
    -- value of the comparison map at `[p, k]` is substituted by `congrArg`.
    refine (congrArg (fun q : Extend (Extend s.P σ hσ) τ hτ x ↦
      TotalSpace.mk' F (((s.extend σ hσ hσρ hρ'n hρ'c).extend τ hτ hτρ hρ''n hρ''c).toFrame
        ⟨x, q⟩).proj ((((s.extend σ hσ hσρ hρ'n hρ'c).extend τ hτ hτρ hρ''n hρ''c).toFrame
          ⟨x, q⟩).frame (WithLp.toLp 2 v)))
        (Extend.compEquiv_symm_mk σ hσ τ hτ p k)).trans ?_
    refine ((s.extend σ hσ hσρ hρ'n hρ'c).toFrame_extend_mk τ hτ hτρ hρ''n hρ''c x
      (Extend.inl σ hσ p) k v).trans ?_
    rw [toFrame_extend_inl]
    exact (s.toFrame_extend_mk (τ.comp σ) (hτ.comp hσ) _ hρ''n hρ''c x p k v).symm

@[simp]
theorem extendCompEquiv_toEquiv_mk (x : X) (p : s.P x) (k : K) :
    (s.extendCompEquiv σ hσ hσρ hρ'n hρ'c τ hτ hτρ hρ''n hρ''c).toEquiv x
        (Extend.mk (τ.comp σ) (hτ.comp hσ) p k) =
      Extend.mk τ hτ (Extend.inl σ hσ p) k :=
  Extend.compEquiv_symm_mk σ hσ τ hτ p k

@[simp]
theorem extendCompEquiv_toEquiv_inl (x : X) (p : s.P x) :
    (s.extendCompEquiv σ hσ hσρ hρ'n hρ'c τ hτ hτρ hρ''n hρ''c).toEquiv x
        (Extend.inl (τ.comp σ) (hτ.comp hσ) p) =
      Extend.inl τ hτ (Extend.inl σ hσ p) :=
  Extend.compEquiv_symm_inl σ hσ τ hτ p

/-- The inverse of `TauCeti.OrthonormalFrameLift.extendCompEquiv` sends `[[p, h], k]` to
`[p, τ h * k]`. -/
theorem extendCompEquiv_symm_toEquiv_mk_mk (x : X) (p : s.P x) (h : H) (k : K) :
    (s.extendCompEquiv σ hσ hσρ hρ'n hρ'c τ hτ hτρ hρ''n hρ''c).symm.toEquiv x
        (Extend.mk τ hτ (Extend.mk σ hσ p h) k) =
      Extend.mk (τ.comp σ) (hτ.comp hσ) p (τ h * k) := by
  rw [Equiv.symm_toEquiv]
  exact Extend.compEquiv_mk σ hσ τ hτ p h k

end Comp

end OrthonormalFrameLift

end TauCeti
