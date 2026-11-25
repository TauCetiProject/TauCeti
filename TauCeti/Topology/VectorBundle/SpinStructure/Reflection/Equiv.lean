/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.SpinStructure.Reflection

/-!
# Functoriality and involutivity of orientation reversal

The precomposition `s.precompIsometry f` of a `Spinᶜ` structure with an isometry `f` of `ℝⁿ`
(`TauCeti.SpinCStructure.precompIsometry`) is functorial in `s`: an equivalence `s ≃ t` induces an
equivalence `s.precompIsometry f ≃ t.precompIsometry f`, by `[p, h] ↦ [φ p, h]`. When `f` is an
involution, precomposing twice gives back `s`: the principal bundle of the double precomposition
is `(P ×_σ Spinᶜ(n)) ×_σ Spinᶜ(n) ≅ P ×_{σ²} Spinᶜ(n) = P ×_1 Spinᶜ(n) ≅ P`, and this
identification, `[[p, h], k] ↦ p · σ(h) k`, preserves frames because `f π(h) f = π(σ h)`. In
particular orientation reversal is functorial and involutive:
`s.reverse.reverse ≃ s` (`TauCeti.SpinCStructure.reverseReverseEquiv`).

## Main definitions

* `TauCeti.SpinCStructure.Equiv.precompIsometry`, `TauCeti.SpinCStructure.Equiv.reverse`:
  equivalences of `Spinᶜ` structures induce equivalences of their precompositions and orientation
  reversals.
* `TauCeti.SpinCStructure.precompIsometryPrecompIsometryEquiv`: for an involution `f`,
  `(s.precompIsometry f).precompIsometry f ≃ s`.
* `TauCeti.SpinCStructure.reverseReverseEquiv`: `s.reverse.reverse ≃ s`.
* `TauCeti.OrthonormalFrameLift.Equiv.precomp`: equivalences of lifts induce equivalences of the
  lifts with precomposed frames.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
-/

public section

open Bundle MulOpposite CliffordAlgebra TauCeti.PrincipalBundle

namespace TauCeti

namespace OrthonormalFrameLift

variable {X : Type*} [TopologicalSpace X] {F : Type*} {E : X → Type*}
  [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] {n : ℕ}
  {G : Type*} [Group G] [TopologicalSpace G] {ρ : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)}

/-- **Precomposing frames is functorial**: an equivalence `s ≃ t` of lifts is an equivalence of
the lifts with frames precomposed with `r`. -/
noncomputable def Equiv.precomp {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    (r : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (ρ' : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hr : ∀ g v, ρ g (r (WithLp.toLp 2 v)).ofLp = (r (WithLp.toLp 2 (ρ' g v))).ofLp) :
    (s.precomp r ρ' hr).Equiv (t.precomp r ρ' hr) where
  toEquiv := φ.toEquiv
  continuous_toFun := φ.continuous_toFun
  continuous_invFun := φ.continuous_invFun
  map_smul := φ.map_smul
  toFrame_map x p := congrArg (fun q ↦ (⟨q.proj, r.trans q.frame⟩ :
    OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin n)))) (φ.toFrame_map x p)

@[simp]
theorem Equiv.precomp_toEquiv {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    (r : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (ρ' : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hr : ∀ g v, ρ g (r (WithLp.toLp 2 v)).ofLp = (r (WithLp.toLp 2 (ρ' g v))).ofLp) (x : X) :
    (φ.precomp r ρ' hr).toEquiv x = φ.toEquiv x :=
  (rfl)

end OrthonormalFrameLift

/-- The reflection in a coordinate hyperplane is an involution. -/
theorem realCliffordCoordReflection_apply_apply {n : ℕ} (i : Fin n) (v : Fin n → ℝ) :
    realCliffordCoordReflection i (realCliffordCoordReflection i v) = v := by
  ext j
  rcases eq_or_ne j i with rfl | hj <;> simp [*]

namespace SpinCStructure

open OrthonormalFrameLift

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : X → Type} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ} [NeZero n]

/-- The proof that the standard form on `ℝⁿ`, `n ≥ 1`, is nonzero, on which `Spinᶜ(n)` depends. -/
local notation "hQ" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0)

/-- **Precomposition is functorial**: an equivalence `s ≃ t` of `Spinᶜ` structures induces an
equivalence of their precompositions with `f`, by `[p, h] ↦ [φ p, h]`. -/
noncomputable def Equiv.precompIsometry
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0))
    {s t : SpinCStructure F V n} (φ : s.Equiv t) :
    (s.precompIsometry f).Equiv (t.precompIsometry f) :=
  (φ.precomp (realCliffordIsometryEquivEuclidean f)
      (((QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)).subtype.comp
        (spinCGroup.toSpecialOrthogonal (realCliffordForm n 0) _)).comp (precompIsometryHom f))
      fun g v ↦ by
        simpa using toSpecialOrthogonal_precompIsometryHom_apply f g v).extend
    (ρ' := (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)).subtype.comp
      (spinCGroup.toSpecialOrthogonal (realCliffordForm n 0) hQ))
    (precompIsometryHom f)
    (f.symm.toIsometry.continuous_spinCGroupMap hQ hQ) rfl
    (fun g ↦ TauCeti.CliffordAlgebra.norm_toLp_specialOrthogonalGroup_realCliffordForm_apply n
      (spinCGroup.toSpecialOrthogonal _ _ g))
    (fun v ↦ (TauCeti.CliffordAlgebra.continuous_specialOrthogonalGroup_realCliffordForm_apply n
      v).comp (spinCGroup.continuous_toSpecialOrthogonal_pi _ _))

/-- **Orientation reversal is functorial**: an equivalence `s ≃ t` induces an equivalence
`s.reverse ≃ t.reverse`. -/
noncomputable def Equiv.reverse {s t : SpinCStructure F V n} (φ : s.Equiv t) :
    s.reverse.Equiv t.reverse :=
  SpinCStructure.Equiv.precompIsometry _ φ

/-- The frame of `[p, h]` in the `Spinᶜ` structure induced by a lift is the frame of `p`
composed with the rotation of `h`. -/
private theorem toFrame_extendSpinC_mk {G : Type*} [Group G] [TopologicalSpace G]
    {ρ : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)} (t : OrthonormalFrameLift F V n G ρ)
    (σ : G →* spinCGroup (realCliffordForm n 0) hQ) (hσ : Continuous σ)
    (hσρ : ((QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)).subtype.comp
      (spinCGroup.toSpecialOrthogonal (realCliffordForm n 0) _)).comp σ = ρ)
    (x : X) (p : t.P x) (h : spinCGroup (realCliffordForm n 0) hQ) (v : Fin n → ℝ) :
    TotalSpace.mk' F ((t.extendSpinC σ hσ hσρ).toFrame ⟨x, Extend.mk σ hσ p h⟩).proj
        (((t.extendSpinC σ hσ hσρ).toFrame ⟨x, Extend.mk σ hσ p h⟩).frame (WithLp.toLp 2 v)) =
      TotalSpace.mk' F (t.toFrame ⟨x, p⟩).proj ((t.toFrame ⟨x, p⟩).frame (WithLp.toLp 2
        ((spinCGroup.toSpecialOrthogonal _ hQ h : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) v))) :=
  t.toFrame_extend_mk σ hσ hσρ _ _ x p h v

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V] [VectorBundle ℝ F V]
  [NeZero n] in
/-- The frame of `p` in a lift with precomposed frames, applied to `w`, is its frame in the
original lift applied to `r w`. -/
private theorem toFrame_precomp_apply {G : Type*} [Group G] [TopologicalSpace G]
    {ρ : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)} (t : OrthonormalFrameLift F V n G ρ)
    (r : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (ρ' : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hr : ∀ g v, ρ g (r (WithLp.toLp 2 v)).ofLp = (r (WithLp.toLp 2 (ρ' g v))).ofLp)
    (x : X) (p : t.P x) (w : EuclideanSpace ℝ (Fin n)) :
    TotalSpace.mk' F ((t.precomp r ρ' hr).toFrame ⟨x, p⟩).proj
        (((t.precomp r ρ' hr).toFrame ⟨x, p⟩).frame w) =
      TotalSpace.mk' F (t.toFrame ⟨x, p⟩).proj ((t.toFrame ⟨x, p⟩).frame (r w)) :=
  (rfl)

/-- For an involution `f`, the automorphism `[g, z] ↦ [f⁻¹ g, z]` of `Spinᶜ(n)` is an
involution. -/
theorem precompIsometryHom_comp_self
    (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0)) (hf : ∀ v, f (f v) = v) :
    (precompIsometryHom f).comp (precompIsometryHom f) = MonoidHom.id _ := by
  rw [precompIsometryHom, QuadraticMap.Isometry.spinCGroupMap_comp]
  convert QuadraticMap.Isometry.spinCGroupMap_id hQ
  ext v
  have h : f.symm v = f v := f.symm_apply_eq.mpr (hf v).symm
  simp [h]

variable (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0))
  (hf : ∀ v, f (f v) = v) (s : SpinCStructure F V n)

/-- The fibre map of `TauCeti.SpinCStructure.precompIsometryPrecompIsometryEquiv`:
`[[p, h], k] ↦ p · σ(h) k`. -/
private noncomputable def doubleExtendEquiv (x : X) :
    Extend (Extend s.P (precompIsometryHom f) (f.symm.toIsometry.continuous_spinCGroupMap hQ hQ))
        (precompIsometryHom f) (f.symm.toIsometry.continuous_spinCGroupMap hQ hQ) x ≃ s.P x :=
  (Extend.compEquiv _ _ _ _ x).trans
    ((Extend.congrEquiv (precompIsometryHom_comp_self f hf) _ continuous_id x).trans
      (Extend.idEquiv x))

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V] [VectorBundle ℝ F V] in
private theorem doubleExtendEquiv_mk (x : X) (p : s.P x)
    (h k : spinCGroup (realCliffordForm n 0) hQ) :
    doubleExtendEquiv f hf s x (Extend.mk _ _ (Extend.mk _ _ p h) k) =
      op (precompIsometryHom f h * k) • p := by
  simp [doubleExtendEquiv]

private theorem doubleExtendEquiv_smul (x : X) (g : spinCGroup (realCliffordForm n 0) hQ)
    (z : ((s.precompIsometry f).precompIsometry f).P x) :
    doubleExtendEquiv f hf s x (op g • z) = op g • doubleExtendEquiv f hf s x z :=
  (congrArg (Extend.idEquiv x) ((congrArg (Extend.congrEquiv _ _ _ x)
    (Extend.compEquiv_smul _ _ _ _ x g z)).trans (Extend.congrEquiv_smul _ _ _ x g _))).trans
    (Extend.idEquiv_smul x g _)

/-- The homeomorphism of total spaces of `doubleExtendEquiv`. -/
private noncomputable def doubleExtendHomeomorph :
    TotalSpace (spinCGroup (realCliffordForm n 0) hQ)
        (Extend (Extend s.P (precompIsometryHom f)
          (f.symm.toIsometry.continuous_spinCGroupMap hQ hQ))
        (precompIsometryHom f) (f.symm.toIsometry.continuous_spinCGroupMap hQ hQ)) ≃ₜ
      TotalSpace (spinCGroup (realCliffordForm n 0) hQ) s.P :=
  (Extend.compHomeomorph (P := s.P) _ _ _ _).trans ((Extend.congrHomeomorph (P := s.P)
    (precompIsometryHom_comp_self f hf) _ continuous_id).trans (Extend.idHomeomorph (P := s.P)))

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V] [VectorBundle ℝ F V] in
private theorem doubleExtendHomeomorph_apply (z) :
    doubleExtendHomeomorph f hf s z = ⟨z.proj, doubleExtendEquiv f hf s z.proj z.snd⟩ := by
  simp only [doubleExtendHomeomorph, Homeomorph.trans_apply, Extend.compHomeomorph_apply,
    Extend.congrHomeomorph_apply, Extend.idHomeomorph_apply]
  rfl

/-- **Precomposing twice with an involution gives back the structure**: for an involution `f`
of `ℝⁿ`, `(s.precompIsometry f).precompIsometry f ≃ s`, by `[[p, h], k] ↦ p · σ(h) k` for the
automorphism `σ` of `Spinᶜ(n)` induced by `f`. -/
noncomputable def precompIsometryPrecompIsometryEquiv :
    ((s.precompIsometry f).precompIsometry f).Equiv s where
  toEquiv := doubleExtendEquiv f hf s
  continuous_toFun := (doubleExtendHomeomorph f hf s).continuous.congr
    (doubleExtendHomeomorph_apply f hf s)
  continuous_invFun := (doubleExtendHomeomorph f hf s).symm.continuous.congr fun z ↦
    (doubleExtendHomeomorph f hf s).symm_apply_eq.mpr ((doubleExtendHomeomorph_apply f hf s _).trans
      (congrArg (TotalSpace.mk z.proj)
        ((doubleExtendEquiv f hf s z.proj).apply_symm_apply z.snd))).symm
  map_smul x z g := doubleExtendEquiv_smul f hf s x g z
  toFrame_map x z := by
    obtain ⟨q, k, rfl⟩ := Extend.exists_mk (P := Extend s.P (precompIsometryHom f)
      (f.symm.toIsometry.continuous_spinCGroupMap hQ hQ)) (ρ := precompIsometryHom f)
      (hρ := f.symm.toIsometry.continuous_spinCGroupMap hQ hQ) (b := x) z
    obtain ⟨p, h, rfl⟩ := Extend.exists_mk (P := s.P) (ρ := precompIsometryHom f)
      (hρ := f.symm.toIsometry.continuous_spinCGroupMap hQ hQ) (b := x) q
    refine OrthonormalFrameBundle.ext_totalSpaceMk fun v ↦ ?_
    refine (congrArg (fun q : s.P x ↦ TotalSpace.mk' F (s.toFrame ⟨x, q⟩).proj
      ((s.toFrame ⟨x, q⟩).frame (WithLp.toLp 2 v))) (doubleExtendEquiv_mk f hf s x p h k)).trans ?_
    rw [s.toFrame_smul]
    refine Eq.trans ?_ (toFrame_extendSpinC_mk _ _ _ rfl x _ k v).symm
    refine Eq.trans ?_ (toFrame_precomp_apply _ _ _ _ x _ _).symm
    refine Eq.trans ?_ (toFrame_extendSpinC_mk (s.precomp (realCliffordIsometryEquivEuclidean f)
      _ _) (precompIsometryHom f) _ rfl x p h ((realCliffordIsometryEquivEuclidean f)
        (WithLp.toLp 2 _)).ofLp).symm
    refine Eq.trans ?_ (toFrame_precomp_apply _ _ _ _ x _ _).symm
    have key (w : Fin n → ℝ) :
        f ((spinCGroup.toSpecialOrthogonal _ hQ h : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (f w)) =
          (spinCGroup.toSpecialOrthogonal _ hQ (precompIsometryHom f h) :
            (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) w := by
      rw [toSpecialOrthogonal_precompIsometryHom_apply, hf]
    simp only [realCliffordIsometryEquivEuclidean_apply, WithLp.ofLp_toLp, key,
      MonoidHom.comp_apply, map_mul, Subgroup.coe_subtype, mul_apply_eq_comp]

/-- **Orientation reversal is involutive**: `s.reverse.reverse ≃ s`. -/
noncomputable def reverseReverseEquiv : s.reverse.reverse.Equiv s :=
  precompIsometryPrecompIsometryEquiv _ (TauCeti.realCliffordCoordReflection_apply_apply 0) s

end SpinCStructure

end TauCeti
