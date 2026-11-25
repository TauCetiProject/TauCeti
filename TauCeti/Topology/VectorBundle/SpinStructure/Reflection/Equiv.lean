/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.SpinStructure.Reflection.Basic

/-!
# Functoriality and involutivity of orientation reversal

The precomposition `s.precompIsometry f` of a `Spinᶜ` structure with an isometry `f` of `ℝⁿ`
(`TauCeti.SpinCStructure.precompIsometry`) is functorial in `s`: an equivalence `s ≃ t` induces an
equivalence `s.precompIsometry f ≃ t.precompIsometry f`, by `[p, h] ↦ [φ p, h]`. It is also
functorial in `f`. Precomposing with `f` and then with `g` is precomposing with `f ∘ g`: the
principal bundle of the double precomposition is
`(P ×_{σ_f} Spinᶜ(n)) ×_{σ_g} Spinᶜ(n) ≅ P ×_{σ_g σ_f} Spinᶜ(n) = P ×_{σ_{f ∘ g}} Spinᶜ(n)`, and
this identification, `[[p, h], k] ↦ [p, σ_g(h) k]`, preserves frames because
`π(h) g = g π(σ_g h)`. Precomposing with the identity gives back `s`, by `[p, h] ↦ p · h`. In
particular orientation reversal is functorial and involutive:
`s.reverse.reverse ≃ s` (`TauCeti.SpinCStructure.reverseReverseEquiv`).

## Main definitions

* `TauCeti.OrthonormalFrameLift.Equiv.precompIsometry`,
  `TauCeti.OrthonormalFrameLift.Equiv.reverse`: equivalences of `Spinᶜ` structures induce
  equivalences of their precompositions and orientation reversals.
* `TauCeti.SpinCStructure.precompIsometryPrecompIsometryEquiv`:
  `(s.precompIsometry f).precompIsometry g ≃ s.precompIsometry (f ∘ g)`.
* `TauCeti.SpinCStructure.precompIsometryEquivOfEqRefl`: `s.precompIsometry f ≃ s` when `f` is the
  identity.
* `TauCeti.SpinCStructure.reverseReverseEquiv`: `s.reverse.reverse ≃ s`.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
-/

public section

open Bundle MulOpposite CliffordAlgebra TauCeti.PrincipalBundle

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : X → Type} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ} [NeZero n]

/-- The proof that the standard form on `ℝⁿ`, `n ≥ 1`, is nonzero, on which `Spinᶜ(n)` depends. -/
local notation "hQ" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0)

/-- The rotation homomorphism `Spinᶜ(n) → SO(n) ⊆ GL(ℝⁿ)`, along which `Spinᶜ` structures lift the
orthonormal frame bundle. -/
local notation "πᶜ" => MonoidHom.comp
  (Subgroup.subtype (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)))
  (spinCGroup.toSpecialOrthogonal (realCliffordForm n 0) hQ)

/-! ### Functoriality in the structure -/

namespace OrthonormalFrameLift

open SpinCStructure

/-- **Precomposition is functorial**: an equivalence `s ≃ t` of `Spinᶜ` structures induces an
equivalence of their precompositions with `f`, by `[p, h] ↦ [φ p, h]`. -/
noncomputable def Equiv.precompIsometry
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0))
    {s t : SpinCStructure F V n} (φ : s.Equiv t) :
    (s.precompIsometry f).Equiv (t.precompIsometry f) :=
  (φ.precomp (realCliffordIsometryEquivEuclidean f) ((πᶜ).comp (precompIsometryHom f))
      (toSpecialOrthogonal_realCliffordIsometryEquivEuclidean_apply f)).extend (ρ' := πᶜ)
    (precompIsometryHom f) (continuous_precompIsometryHom f) rfl
    spinCGroup.norm_toLp_toSpecialOrthogonal_apply spinCGroup.continuous_toSpecialOrthogonal_apply

@[simp]
theorem Equiv.precompIsometry_toEquiv_mk
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0))
    {s t : SpinCStructure F V n} (φ : s.Equiv t) (x : X) (p : s.P x)
    (h : spinCGroup (realCliffordForm n 0) hQ) :
    (φ.precompIsometry f).toEquiv x
        (Extend.mk (precompIsometryHom f) (continuous_precompIsometryHom f) p h) =
      Extend.mk (precompIsometryHom f) (continuous_precompIsometryHom f)
        (φ.toEquiv x p) h := by
  unfold Equiv.precompIsometry
  refine (Equiv.extend_toEquiv_mk (ρ' := πᶜ) (precompIsometryHom f)
    (continuous_precompIsometryHom f) rfl _ _
    (φ.precomp (realCliffordIsometryEquivEuclidean f) _ _) x p h).trans ?_
  exact congrArg (Extend.mk _ _ · h) (DFunLike.congr_fun (Equiv.precomp_toEquiv φ _ _ _ x) p)

/-- **Orientation reversal is functorial**: an equivalence `s ≃ t` induces an equivalence
`s.reverse ≃ t.reverse`. -/
noncomputable def Equiv.reverse {s t : SpinCStructure F V n} (φ : s.Equiv t) :
    s.reverse.Equiv t.reverse :=
  φ.precompIsometry _

@[simp]
theorem Equiv.reverse_toEquiv_mk {s t : SpinCStructure F V n} (φ : s.Equiv t) (x : X)
    (p : s.P x) (h : spinCGroup (realCliffordForm n 0) hQ) :
    φ.reverse.toEquiv x
      (Extend.mk (precompIsometryHom (realCliffordCoordReflection 0))
        (continuous_precompIsometryHom (realCliffordCoordReflection 0)) p h) =
      Extend.mk (precompIsometryHom (realCliffordCoordReflection 0))
        (continuous_precompIsometryHom (realCliffordCoordReflection 0))
        (φ.toEquiv x p) h :=
  Equiv.precompIsometry_toEquiv_mk _ φ x p h

end OrthonormalFrameLift

/-! ### Functoriality in the isometry -/

namespace SpinCStructure

open OrthonormalFrameLift

/-- **Precomposing twice is precomposing with the composite**:
`(s.precompIsometry f).precompIsometry g ≃ s.precompIsometry (f ∘ g)`, by
`[[p, h], k] ↦ [p, σ_g(h) k]`, where `σ_g` is the automorphism of `Spinᶜ(n)` induced by `g`
(`TauCeti.SpinCStructure.precompIsometryHom`). Frames match because `π(h) g = g π(σ_g h)`
(`TauCeti.SpinCStructure.toSpecialOrthogonal_precompIsometryHom_apply`). -/
noncomputable def precompIsometryPrecompIsometryEquiv
    (f g : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0))
    (s : SpinCStructure F V n) :
    ((s.precompIsometry f).precompIsometry g).Equiv (s.precompIsometry (g.trans f)) :=
  ((s.precompIsometry f).precompIsometryLift g).extendSpinCEquivOfEquivariant
    (precompIsometryHom g) (continuous_precompIsometryHom g) rfl (s.precompIsometry (g.trans f))
    (fun x q ↦ Extend.congrEquiv (precompIsometryHom_comp f g) _ _ x
      (Extend.compEquiv _ _ _ _ x (Extend.inl (P := Extend s.P (precompIsometryHom f)
        (continuous_precompIsometryHom f)) (precompIsometryHom g)
          (continuous_precompIsometryHom g) q)))
    (fun x q k ↦ (congrArg (Extend.congrEquiv (precompIsometryHom_comp f g) _ _ x)
      ((congrArg (Extend.compEquiv _ _ _ _ x) (Extend.inl_smul _ _ q k)).trans
        (Extend.compEquiv_smul _ _ _ _ x _ _))).trans (Extend.congrEquiv_smul _ _ _ x _ _))
    (((Extend.congrHomeomorph (precompIsometryHom_comp f g) _ _).continuous.comp
      ((Extend.compHomeomorph _ _ _ _).continuous.comp
        (Extend.continuous_inl (Extend s.P (precompIsometryHom f)
          (continuous_precompIsometryHom f)) (precompIsometryHom g)
            (continuous_precompIsometryHom g)))).congr
        fun z ↦ (congrArg (Extend.congrHomeomorph (precompIsometryHom_comp f g) _ _)
          (Extend.compHomeomorph_apply _ _ _ _ _)).trans (Extend.congrHomeomorph_apply _ _ _ _))
    fun x q ↦ by
      obtain ⟨p, h, rfl⟩ := Extend.exists_mk (P := s.P) (ρ := precompIsometryHom f)
        (hρ := continuous_precompIsometryHom f) (b := x) q
      refine OrthonormalFrameBundle.ext_totalSpaceMk fun v ↦ ?_
      have hφ : Extend.congrEquiv (precompIsometryHom_comp f g) _ _ x
          (Extend.compEquiv _ _ _ _ x (Extend.inl (precompIsometryHom g)
            (continuous_precompIsometryHom g) (Extend.mk (precompIsometryHom f)
              (continuous_precompIsometryHom f) p h))) =
          Extend.mk (precompIsometryHom (g.trans f))
            (continuous_precompIsometryHom (g.trans f)) p
            (precompIsometryHom g h) := by
        rw [Extend.inl_def, Extend.compEquiv_mk, mul_one, Extend.congrEquiv_mk]
      -- `rw` cannot see through the fibre `(s.precompIsometry _).P x = Extend s.P _ _ x`, so the
      -- value of the comparison map at `[p, h]` is substituted by `congrArg`.
      refine (congrArg (fun q : (s.precompIsometry (g.trans f)).P x ↦
        TotalSpace.mk' F ((s.precompIsometry (g.trans f)).toFrame ⟨x, q⟩).proj
          (((s.precompIsometry (g.trans f)).toFrame ⟨x, q⟩).frame (WithLp.toLp 2 v))) hφ).trans ?_
      -- Both sides are frames of points `[p, k]` of extensions: the frame of `p` composed with
      -- the rotation of `k`.
      refine (toFrame_extend_mk (s.precompIsometryLift (g.trans f))
        (precompIsometryHom (g.trans f)) _ rfl _ spinCGroup.continuous_toSpecialOrthogonal_apply x p
        _ v).trans ?_
      refine Eq.trans ?_ (toFrame_extend_mk (s.precompIsometryLift f)
        (precompIsometryHom f) _ rfl _ spinCGroup.continuous_toSpecialOrthogonal_apply x p h
          ((realCliffordIsometryEquivEuclidean g) (WithLp.toLp 2 v)).ofLp).symm
      -- Unfolding the precompositions (`toFrame_precomp`), both sides are frames of `p`, at
      -- `(f ∘ g) π(σ_g h) v` and `f π(h) g v`, which agree.
      calc _ = TotalSpace.mk' F (s.toFrame ⟨x, p⟩).proj ((s.toFrame ⟨x, p⟩).frame
            (realCliffordIsometryEquivEuclidean (g.trans f) (WithLp.toLp 2
              ((spinCGroup.toSpecialOrthogonal _ hQ (precompIsometryHom g h) :
                (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) v)))) := rfl
        _ = TotalSpace.mk' F (s.toFrame ⟨x, p⟩).proj ((s.toFrame ⟨x, p⟩).frame
            (realCliffordIsometryEquivEuclidean f (WithLp.toLp 2
              ((spinCGroup.toSpecialOrthogonal _ hQ h : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
                (realCliffordIsometryEquivEuclidean g (WithLp.toLp 2 v)).ofLp)))) := by
          rw [realCliffordIsometryEquivEuclidean_apply, realCliffordIsometryEquivEuclidean_apply,
            WithLp.ofLp_toLp, realCliffordIsometryEquivEuclidean_apply,
            toSpecialOrthogonal_precompIsometryHom_apply]
          -- `(g.trans f) w` is `f (g w)` by definition.
          rfl
        _ = _ := rfl

@[simp]
theorem precompIsometryPrecompIsometryEquiv_toEquiv_mk
    (f g : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0))
    (s : SpinCStructure F V n) (x : X) (p : s.P x) (h k : spinCGroup (realCliffordForm n 0) hQ) :
    (precompIsometryPrecompIsometryEquiv f g s).toEquiv x
        (Extend.mk (precompIsometryHom g) (continuous_precompIsometryHom g)
          (Extend.mk (precompIsometryHom f) (continuous_precompIsometryHom f) p h)
          k) =
      Extend.mk (precompIsometryHom (g.trans f))
        (continuous_precompIsometryHom (g.trans f)) p
        (precompIsometryHom g h * k) := by
  unfold precompIsometryPrecompIsometryEquiv
  refine (extendSpinCEquivOfEquivariant_toEquiv_mk ..).trans ?_
  rw [Extend.inl_def, Extend.compEquiv_mk, mul_one, Extend.congrEquiv_mk]
  exact Extend.smul_mk _ _ _ _ _

/-- **Precomposing with the identity gives back the structure**: if `f` is the identity of
`ℝⁿ`, then `s.precompIsometry f ≃ s`, by `[p, h] ↦ p · h`. The isometry is a variable with
`hf : f = refl`, rather than `refl` itself, so that this applies without casts to isometries that
are only propositionally the identity, such as `f ∘ f` for an involution `f`. -/
noncomputable def precompIsometryEquivOfEqRefl
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0))
    (hf : f = QuadraticMap.IsometryEquiv.refl _) (s : SpinCStructure F V n) :
    (s.precompIsometry f).Equiv s :=
  (s.precompIsometryLift f).extendSpinCEquivOfEquivariant
    (precompIsometryHom f) (continuous_precompIsometryHom f) rfl s (fun _ p ↦ p)
    (fun x p g ↦ by
      subst hf
      exact congrArg (fun k ↦ op k • p) (precompIsometryHom_refl_apply g).symm)
    continuous_id
    fun x p ↦ by
      subst hf
      refine OrthonormalFrameBundle.ext_totalSpaceMk fun v ↦ ?_
      -- The frame of `p` precomposed with the identity (`toFrame_precomp`) is the frame of `p`.
      calc _ = TotalSpace.mk' F (s.toFrame ⟨x, p⟩).proj ((s.toFrame ⟨x, p⟩).frame
            (realCliffordIsometryEquivEuclidean (QuadraticMap.IsometryEquiv.refl _)
              (WithLp.toLp 2 v))) := by
            rw [realCliffordIsometryEquivEuclidean_apply]
            -- `refl v` is `v` by definition.
            rfl
        _ = _ := rfl

@[simp]
theorem precompIsometryEquivOfEqRefl_toEquiv_mk
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0))
    (hf : f = QuadraticMap.IsometryEquiv.refl _) (s : SpinCStructure F V n) (x : X) (p : s.P x)
    (h : spinCGroup (realCliffordForm n 0) hQ) :
    (precompIsometryEquivOfEqRefl f hf s).toEquiv x
        (Extend.mk (precompIsometryHom f) (continuous_precompIsometryHom f) p h) =
      op h • p := by
  unfold precompIsometryEquivOfEqRefl
  exact extendSpinCEquivOfEquivariant_toEquiv_mk ..

/-- **Orientation reversal is involutive**: `s.reverse.reverse ≃ s`, by
`[[p, h], k] ↦ p · σ(h) k` for the automorphism `σ` of `Spinᶜ(n)` induced by the reflection. -/
noncomputable def reverseReverseEquiv (s : SpinCStructure F V n) : s.reverse.reverse.Equiv s :=
  (precompIsometryPrecompIsometryEquiv _ _ s).trans (precompIsometryEquivOfEqRefl _
    (DFunLike.ext _ _ fun v ↦ realCliffordCoordReflection_involutive 0 v) s)

@[simp]
theorem reverseReverseEquiv_toEquiv_mk (s : SpinCStructure F V n) (x : X) (p : s.P x)
    (h k : spinCGroup (realCliffordForm n 0) hQ) :
    (reverseReverseEquiv s).toEquiv x
        (Extend.mk (precompIsometryHom (realCliffordCoordReflection 0))
          (continuous_precompIsometryHom (realCliffordCoordReflection 0))
          (Extend.mk (precompIsometryHom (realCliffordCoordReflection 0))
            (continuous_precompIsometryHom (realCliffordCoordReflection 0)) p h)
          k) =
      op (precompIsometryHom (realCliffordCoordReflection 0) h * k) • p := by
  rw [reverseReverseEquiv, OrthonormalFrameLift.Equiv.trans_toEquiv]
  exact (congrArg ((precompIsometryEquivOfEqRefl _ _ s).toEquiv x)
    (precompIsometryPrecompIsometryEquiv_toEquiv_mk _ _ s x p h k)).trans
      (precompIsometryEquivOfEqRefl_toEquiv_mk _ _ s x p _)

end SpinCStructure

end TauCeti
