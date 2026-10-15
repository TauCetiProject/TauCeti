/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.ContinuousAut.Quotient
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Rank
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Surjective
import TauCeti.Topology.Algebra.Group.Profinite.ProP.FiniteGeneration

/-!
# Continuous automorphisms of a free pro-`p` group of finite rank

Let `F` be a topological group with a topological isomorphism `e : F ≃ₜ* freeProP p X` to the free
pro-`p` group on a finite type `X`, so that `x i := e.symm (freeProP.of i)` is a basis of `F`.
A continuous automorphism of `F` is prescribed by its values on the basis, and any family of values
that topologically generates `F` is attained: the endomorphism `x i ↦ y i` given by the universal
property is surjective, hence bijective by the Hopf property of topologically finitely generated
profinite groups.

The main source of such families is the following: if each `y i` is a conjugate of the `p`-adic
power of `x i` by a unit `u i`, then the `y i` generate by Burnside's basis theorem, since modulo
the Frattini subgroup conjugation is trivial and `x i ^ u i` generates the same closed subgroup as
`x i`. So for every family of units `u i` and every choice of conjugators `c i` there is a
continuous automorphism with `x i ↦ (c i)⁻¹ * x i ^ u i * c i`. This is the automorphism criterion
by which endomorphisms of a free pro-`p` group given on a basis by conjugated unit powers, such as
the automorphisms of free pro-`p` groups preserving the peripheral conjugacy classes up to a common
exponent, are shown to be automorphisms.

Burnside's basis theorem also shows that every abstract automorphism `σ` of the Frattini quotient
`freeProP p X ⧸ proPFrattini p (freeProP p X)` comes from a continuous automorphism: lifts of the
images under `σ` of the classes of the generators `of i` generate the free group, so the
automorphism sending each `of i` to such a lift induces `σ`. Hence the map
`ContinuousAut (freeProP p X) →* MulAut (freeProP p X ⧸ proPFrattini p _)` is surjective. Its
target is the automorphism group of the `𝔽_p`-vector space with basis the classes of the
generators (`TauCeti.freeProP.frattiniQuotientBasis`), that is `GL_n(𝔽_p)` for `X = Fin n`.

## Main definitions

* `TauCeti.freeProP.finSuccExtend`: the automorphism of the free pro-`p` group on `Fin (n + 1)`
  fixing the first generator and acting on the others through a given automorphism of the free
  pro-`p` group on `Fin n`.

## Main results

* `TauCeti.freeProP.finSuccExtend_map_succ`: the extension along `Fin.succ` intertwines
  `freeProP.map Fin.succ` with the given automorphism; `TauCeti.freeProP.finSuccExtend_refl`,
  `TauCeti.freeProP.finSuccExtend_trans` and `TauCeti.freeProP.finSuccExtend_symm` say that it
  is compatible with the identity, composition and inversion.
* `TauCeti.freeProP.exists_continuousAut_of_topologicallyGenerates`: every topological generating
  family of `F` indexed by `X` is the image of the basis under a continuous automorphism.
* `TauCeti.freeProP.mapQuotient_proPFrattini_surjective`: every automorphism of the Frattini
  quotient of the free pro-`p` group of finite rank is induced by a continuous automorphism.
* `TauCeti.IsProP.exists_continuousAut_apply_eq_conj_padicPow`: for every family of units `u` and
  every family of conjugators `c`, some continuous automorphism of `F` sends `x i` to
  `(c i)⁻¹ * x i ^ u i * c i`.
* `TauCeti.IsProP.exists_continuousAut_apply_eq_conj_padicPow_const`: the special case of a common
  unit `u`, sending `x i` to `(c i)⁻¹ * x i ^ u * c i`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, 2nd ed., Proposition 2.5.2 (the Hopf property),
  Proposition 2.8.7 (Burnside's basis theorem) and §4.5 (automorphisms of free pro-`p` groups).
-/

public section

namespace TauCeti

universe u v

variable {p : ℕ} {X : Type u}

namespace freeProP

section FinSucc

variable {n : ℕ}

/-- The continuous endomorphism of `freeProP p (Fin (n + 1))` fixing the first generator and
acting on the others through `e` intertwines `map Fin.succ` with `e`: both composites agree on the
generators. -/
private theorem lift_cons_comp_map_succ (e : freeProP p (Fin n) →ₜ* freeProP p (Fin n)) :
    (lift (isProP_freeProP p _) (Fin.cons (of 0) fun j ↦ map Fin.succ (e (of j)))).comp
      (map (Fin.succ : Fin n → Fin (n + 1))) = (map Fin.succ).comp e :=
  hom_ext fun j ↦ by simp

/-- The two continuous endomorphisms of `freeProP p (Fin (n + 1))` fixing the first generator and
acting on the others through `e₁`, resp. `e₂`, compose to the one acting through `e₁ ∘ e₂`. -/
private theorem lift_cons_comp_lift_cons (e₁ e₂ : freeProP p (Fin n) →ₜ* freeProP p (Fin n)) :
    (lift (isProP_freeProP p _) (Fin.cons (of 0) fun j ↦ map Fin.succ (e₁ (of j)))).comp
        (lift (isProP_freeProP p _) (Fin.cons (of 0) fun j ↦ map Fin.succ (e₂ (of j)))) =
      lift (isProP_freeProP p _) (Fin.cons (of 0) fun j ↦ map Fin.succ (e₁ (e₂ (of j)))) := by
  refine hom_ext fun i ↦ Fin.cases (by simp) (fun j ↦ ?_) i
  simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply, lift_of, Fin.cons_succ]
  have h := DFunLike.congr_fun (lift_cons_comp_map_succ e₁) (e₂ (of j))
  simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply] at h
  exact h

/-- The continuous endomorphism of `freeProP p (Fin (n + 1))` fixing the first generator and
acting on the others through the identity is the identity. -/
private theorem lift_cons_id :
    lift (isProP_freeProP p _) (Fin.cons (of 0) fun j : Fin n ↦ map Fin.succ (of j)) =
      ContinuousMonoidHom.id (freeProP p (Fin (n + 1))) :=
  hom_ext fun i ↦ Fin.cases (by simp) (fun j ↦ by simp) i

/-- **Extension of an automorphism along `Fin.succ`.** For a continuous automorphism `e` of the
free pro-`p` group on `Fin n`, the continuous automorphism of the free pro-`p` group on
`Fin (n + 1)` fixing the first generator `x₀` and acting on the remaining generators
`x_{j+1}`, `j : Fin n`, through `e`, read in `freeProP p (Fin (n + 1))` along
`freeProP.map Fin.succ` (`TauCeti.freeProP.finSuccExtend_map_succ`). Its inverse is the extension
of `e.symm`. -/
noncomputable def finSuccExtend (e : freeProP p (Fin n) ≃ₜ* freeProP p (Fin n)) :
    freeProP p (Fin (n + 1)) ≃ₜ* freeProP p (Fin (n + 1)) where
  toFun := lift (isProP_freeProP p _) (Fin.cons (of 0) fun j ↦ map Fin.succ (e (of j)))
  invFun := lift (isProP_freeProP p _) (Fin.cons (of 0) fun j ↦ map Fin.succ (e.symm (of j)))
  left_inv y := by
    have h := lift_cons_comp_lift_cons (p := p) (e.symm : freeProP p (Fin n) →ₜ* freeProP p (Fin n))
      (e : freeProP p (Fin n) →ₜ* freeProP p (Fin n))
    simp only [ContinuousMonoidHom.coe_coe, ContinuousMulEquiv.symm_apply_apply, lift_cons_id] at h
    simpa using DFunLike.congr_fun h y
  right_inv y := by
    have h := lift_cons_comp_lift_cons (p := p) (e : freeProP p (Fin n) →ₜ* freeProP p (Fin n))
      (e.symm : freeProP p (Fin n) →ₜ* freeProP p (Fin n))
    simp only [ContinuousMonoidHom.coe_coe, ContinuousMulEquiv.apply_symm_apply, lift_cons_id] at h
    simpa using DFunLike.congr_fun h y
  map_mul' := map_mul _
  continuous_toFun := (lift _ _).continuous
  continuous_invFun := (lift _ _).continuous

variable (e : freeProP p (Fin n) ≃ₜ* freeProP p (Fin n))

/-- The extension of `e` along `Fin.succ` is the lift of the family fixing the first generator and
reading `e` on the others. -/
private theorem coe_finSuccExtend :
    ⇑(finSuccExtend e) =
      ⇑(lift (isProP_freeProP p _) (Fin.cons (of 0) fun j ↦ map Fin.succ (e (of j)))) :=
  rfl

/-- The extension of `e` along `Fin.succ` fixes the first generator. -/
@[simp]
theorem finSuccExtend_of_zero : finSuccExtend e (of 0) = of 0 := by
  rw [coe_finSuccExtend, lift_of, Fin.cons_zero]

/-- The extension of `e` along `Fin.succ` acts on the generator at `j.succ` through `e`. -/
@[simp]
theorem finSuccExtend_of_succ (j : Fin n) :
    finSuccExtend e (of j.succ) = map Fin.succ (e (of j)) := by
  rw [coe_finSuccExtend, lift_of, Fin.cons_succ]

/-- The extension of `e` along `Fin.succ` intertwines `freeProP.map Fin.succ` with `e`. -/
@[simp]
theorem finSuccExtend_map_succ (y : freeProP p (Fin n)) :
    finSuccExtend e (map (Fin.succ : Fin n → Fin (n + 1)) y) = map Fin.succ (e y) := by
  rw [coe_finSuccExtend]
  exact DFunLike.congr_fun (lift_cons_comp_map_succ (e : freeProP p (Fin n) →ₜ* freeProP p (Fin n)))
    y

/-- The inverse of the extension of `e` along `Fin.succ` is the extension of `e.symm`. -/
@[simp]
theorem finSuccExtend_symm : (finSuccExtend e).symm = finSuccExtend e.symm :=
  ContinuousMulEquiv.ext fun _ ↦ rfl

/-- The extension of the identity along `Fin.succ` is the identity. -/
@[simp]
theorem finSuccExtend_refl :
    finSuccExtend (ContinuousMulEquiv.refl (freeProP p (Fin n))) = ContinuousMulEquiv.refl _ :=
  ContinuousMulEquiv.ext fun y ↦ by
    rw [coe_finSuccExtend]
    exact DFunLike.congr_fun (lift_cons_id (p := p) (n := n)) y

/-- Extension along `Fin.succ` is compatible with composition. -/
@[simp]
theorem finSuccExtend_trans (e₁ e₂ : freeProP p (Fin n) ≃ₜ* freeProP p (Fin n)) :
    finSuccExtend (e₁.trans e₂) = (finSuccExtend e₁).trans (finSuccExtend e₂) :=
  ContinuousMulEquiv.ext fun y ↦ by
    rw [ContinuousMulEquiv.trans_apply, coe_finSuccExtend, coe_finSuccExtend, coe_finSuccExtend]
    exact (DFunLike.congr_fun (lift_cons_comp_lift_cons
      (e₂ : freeProP p (Fin n) →ₜ* freeProP p (Fin n))
      (e₁ : freeProP p (Fin n) →ₜ* freeProP p (Fin n))) y).symm

/-- The extension of `e` along `Fin.succ` fixes the first `ℕ`-indexed generator. -/
theorem finSuccExtend_freeProPGen_zero :
    finSuccExtend e (freeProPGen p (n + 1) 0) = freeProPGen p (n + 1) 0 := by
  rw [freeProPGen_of_lt p n.succ_pos, Fin.zero_eta, finSuccExtend_of_zero]

end FinSucc

variable [Finite X]

/-- **Generating families are images of the basis under automorphisms.** If `F` is a free pro-`p`
group on the finite type `X`, with basis `x i := e.symm (of i)`, then every family `y : X → F`
that topologically generates `F` is the image of the basis under a continuous automorphism of
`F`. -/
theorem exists_continuousAut_of_topologicallyGenerates {F : Type v} [Group F] [TopologicalSpace F]
    [IsTopologicalGroup F] (e : F ≃ₜ* freeProP p X) {y : X → F}
    (hy : (Subgroup.closure (Set.range y)).topologicalClosure = ⊤) :
    ∃ φ : ContinuousAut F, ∀ i, φ (e.symm (of i)) = y i := by
  have hey : (Subgroup.closure (Set.range (e ∘ y))).topologicalClosure = ⊤ := by
    rw [Set.range_comp]
    exact topologicalClosure_closure_image_eq_top hy (f := (e : F →* freeProP p X))
      e.continuous e.surjective.denseRange
  refine ⟨e.trans ((continuousMulEquivOfTopologicallyGenerates (e ∘ y) hey).trans e.symm),
    fun i ↦ ?_⟩
  simp

/-- **Automorphisms of the Frattini quotient of a free pro-`p` group lift.** For a prime `p` and a
finite type `X`, every abstract automorphism `σ` of the Frattini quotient
`freeProP p X ⧸ proPFrattini p (freeProP p X)` is induced by a continuous automorphism of the free
pro-`p` group, namely one sending each generator `of i` to a lift of `σ` applied to its class. -/
theorem mapQuotient_proPFrattini_surjective [Fact p.Prime] :
    Function.Surjective
      (ContinuousAut.mapQuotient (isTopCharacteristic_proPFrattini (G := freeProP p X) p)) := by
  intro σ
  let Φ := proPFrattini p (freeProP p X)
  have : DiscreteTopology (freeProP p X ⧸ Φ) := QuotientGroup.discreteTopology
    ((isTopologicallyFinitelyGenerated_freeProP p X).isOpen_proPFrattini p)
  -- Lift the images under `σ` of the classes of the generators.
  choose y hy using fun i ↦ QuotientGroup.mk_surjective (σ (QuotientGroup.mk (s := Φ) (of i)))
  -- In the discrete Frattini quotient, the classes of the generators generate abstractly.
  have hx : Subgroup.closure (QuotientGroup.mk' Φ '' Set.range of) = ⊤ := by
    refine top_unique ?_
    rw [← (topologicallyGenerates_iff_frattiniQuotient (isProP_freeProP p X) _).mp
      (topologicalClosure_closure_range_of_eq_top p X)]
    exact Subgroup.topologicalClosure_minimal _ le_rfl (isClosed_discrete _)
  -- So do their images under `σ`, the classes of the `y i`, and by Burnside's basis theorem the
  -- `y i` generate the free pro-`p` group topologically.
  have hy' : (Subgroup.closure (Set.range y)).topologicalClosure = ⊤ := by
    have himage : QuotientGroup.mk' Φ '' Set.range y =
        σ.toMonoidHom '' (QuotientGroup.mk' Φ '' Set.range of) := by
      simp only [← Set.range_comp]
      congr 1
      funext i
      simp [hy]
    rw [topologicallyGenerates_iff_frattiniQuotient (isProP_freeProP p X), himage,
      ← MonoidHom.map_closure, hx, Subgroup.map_top_of_surjective _ σ.surjective]
    exact top_unique (Subgroup.le_topologicalClosure _)
  refine ⟨continuousMulEquivOfTopologicallyGenerates y hy',
    MulEquiv.toMonoidHom_injective <| MonoidHom.eq_of_eqOn_dense hx ?_⟩
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  simp [hy]

end freeProP

namespace IsProP

variable [Fact p.Prime] [Finite X]

/-- **The automorphism criterion for conjugated unit powers.** If `F` is a free pro-`p` group on
the finite type `X`, with basis `x i := e.symm (freeProP.of i)`, then for every family of units
`u : X → ℤ_[p]ˣ` and every family of conjugators `c : X → F` there is a continuous automorphism of
`F` sending each `x i` to `(c i)⁻¹ * x i ^ u i * c i`. -/
theorem exists_continuousAut_apply_eq_conj_padicPow {F : Type v} [Group F] [TopologicalSpace F]
    [IsTopologicalGroup F] [CompactSpace F] [TotallyDisconnectedSpace F] (hF : IsProP p F)
    (e : F ≃ₜ* freeProP p X) (u : X → ℤ_[p]ˣ) (c : X → F) :
    ∃ φ : ContinuousAut F, ∀ i,
      φ (e.symm (freeProP.of i)) = (c i)⁻¹ * hF.padicPow (e.symm (freeProP.of i)) (u i) * c i := by
  -- The basis generates `F`, being the image of the generators of `freeProP p X` under `e.symm`.
  have hx := topologicalClosure_closure_image_eq_top
    (freeProP.topologicalClosure_closure_range_of_eq_top p X)
    (f := (e.symm : freeProP p X →* F)) e.symm.continuous e.symm.surjective.denseRange
  rw [← Set.range_comp] at hx
  -- `hx` is stated for `⇑(e.symm : freeProP p X →* F) ∘ freeProP.of`, which is the basis by
  -- unfolding the coercion; `x` is given explicitly to keep the conclusion in basis form.
  exact freeProP.exists_continuousAut_of_topologicallyGenerates e <|
    hF.topologicalClosure_closure_range_eq_top_of_isConj_padicPow
      (x := fun i ↦ e.symm (freeProP.of i)) hx u fun i ↦
      isConj_iff.mpr ⟨(c i)⁻¹, by rw [inv_inv]⟩

/-- **The automorphism criterion for conjugated powers with a common unit.** The special case of
`exists_continuousAut_apply_eq_conj_padicPow` in which every basis element `x i` is raised to the
same unit `u` of `ℤ_[p]`: some continuous automorphism of `F` sends each `x i` to
`(c i)⁻¹ * x i ^ u * c i`. -/
theorem exists_continuousAut_apply_eq_conj_padicPow_const {F : Type v} [Group F]
    [TopologicalSpace F] [IsTopologicalGroup F] [CompactSpace F] [TotallyDisconnectedSpace F]
    (hF : IsProP p F) (e : F ≃ₜ* freeProP p X) (u : ℤ_[p]ˣ) (c : X → F) :
    ∃ φ : ContinuousAut F, ∀ i,
      φ (e.symm (freeProP.of i)) = (c i)⁻¹ * hF.padicPow (e.symm (freeProP.of i)) u * c i :=
  hF.exists_continuousAut_apply_eq_conj_padicPow e (fun _ ↦ u) c

end IsProP

end TauCeti
