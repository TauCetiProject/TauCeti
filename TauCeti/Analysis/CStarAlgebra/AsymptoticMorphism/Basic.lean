/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Analysis.CStarAlgebra.Quotient
public import TauCeti.Topology.ContinuousMap.Bounded.TendstoZeroIdeal
import TauCeti.Algebra.Star.Basic
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import TauCeti.Analysis.Normed.Group.Bounded
import TauCeti.Topology.ContinuousMap.Bounded.Normed

/-!
# Asymptotic morphisms of C⋆-algebras

An *asymptotic morphism* from a (possibly nonunital) complex C⋆-algebra `A` to `B` is a family of
maps `φ : Set.Ici (1 : ℝ) → A → B`, continuous in `t ∈ [1, ∞)` for each fixed `a ∈ A`, whose
pointwise addition, `ℂ`-scalar, multiplication, and involution defects converge to `0` in norm as
`t → ∞` (Connes–Higson; Blackadar, Definition 25.1.1). Remarkably, no boundedness or continuity
in `a` is assumed: lifting `φ` to minimal unitizations and decomposing self-adjoint contractions via
`a² + (√(1 - a²))² = 1` forces `t ↦ ‖φ t a‖` to be eventually bounded, hence bounded on `[1, ∞)`.
Passing to `AsymptoticAlgebra B := (Set.Ici (1 : ℝ) →ᵇ B) ⧸ tendstoZeroIdeal B atTop` induces a
`⋆`-homomorphism `φ.toAsymptoticHom : A →⋆ₙₐ[ℂ] AsymptoticAlgebra B`, yielding automatic asymptotic
contractivity `limsup (fun t ↦ ‖φ t a‖) atTop ≤ ‖a‖` (Blackadar, Proposition 25.1.3) and identifying
equivalence classes of asymptotic morphisms with `A →⋆ₙₐ[ℂ] AsymptoticAlgebra B` (Proposition
25.1.4(a)).

## Main definitions and results

* `TauCeti.AsymptoticAlgebra`, `TauCeti.AsymptoticAlgebra.mk`, `TauCeti.AsymptoticAlgebra.mkCLM`,
  and `TauCeti.AsymptoticMorphism`: the asymptotic C⋆-algebra `C_b([1, ∞), B) ⧸ C₀([1, ∞), B)`,
  its quotient `⋆`-homomorphism and continuous linear map, and bundled asymptotic morphisms.
* `TauCeti.AsymptoticMorphism.unitization`: lift to `Unitization ℂ A → Unitization ℂ B`.
* `TauCeti.AsymptoticMorphism.exists_eventually_norm_le`, `TauCeti.AsymptoticMorphism.toBounded`,
  `TauCeti.AsymptoticMorphism.toAsymptoticHom`, and `TauCeti.AsymptoticMorphism.limsup_norm_le`:
  automatic boundedness, the induced `⋆`-homomorphism, and asymptotic contractivity.
* `TauCeti.AsymptoticMorphism.IsAsymptoticallyEquivalent` and
  `TauCeti.AsymptoticMorphism.quotientEquivAsymptoticHom`: asymptotic equivalence and the bijection
  with `A →⋆ₙₐ[ℂ] AsymptoticAlgebra B`.
* `NonUnitalStarAlgHom.toAsymptoticMorphism`, `NonUnitalStarAlgHom.rescaledAsymptoticMorphism`,
  `TauCeti.AsymptoticMorphism.compStarAlgHom`, `TauCeti.AsymptoticMorphism.postcompStarAlgHom`,
  and `TauCeti.AsymptoticMorphism.reparam`: examples, functoriality, and reparameterization.

## References

* Alain Connes and Nigel Higson, *Déformations, morphismes asymptotiques et K-théorie bivariante*,
  C. R. Acad. Sci. Paris Sér. I Math. **311** (1990), no. 2, 101–106.
* Bruce Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications **5**, Cambridge
  University Press, 1998, §25.1 (Definition 25.1.1, Propositions 25.1.3 and 25.1.4(a)).
-/

public section

open Filter Set Topology
open scoped BoundedContinuousFunction ComplexStarModule CStarAlgebra

namespace TauCeti

/-- The asymptotic C⋆-algebra `C_b([1, ∞), B) ⧸ C₀([1, ∞), B)` of a (possibly nonunital) C⋆-algebra
`B`, realized as the quotient of `Set.Ici (1 : ℝ) →ᵇ B` by the closed two-sided ideal of bounded
continuous functions tending to `0` along `atTop`. -/
abbrev AsymptoticAlgebra (B : Type*) [NonUnitalCStarAlgebra B] : Type _ :=
  (Ici (1 : ℝ) →ᵇ B) ⧸ BoundedContinuousFunction.tendstoZeroIdeal B atTop

namespace AsymptoticAlgebra

variable {B : Type*} [NonUnitalCStarAlgebra B]

/-- The canonical surjective `⋆`-homomorphism `(Set.Ici (1 : ℝ) →ᵇ B) →⋆ₙₐ[ℂ] AsymptoticAlgebra B`.
-/
noncomputable def mk : (Ici (1 : ℝ) →ᵇ B) →⋆ₙₐ[ℂ] AsymptoticAlgebra B :=
  TwoSidedIdeal.Quotient.mkStarAlgHom (BoundedContinuousFunction.tendstoZeroIdeal B atTop)

theorem mk_apply (f : Ici (1 : ℝ) →ᵇ B) :
    mk f = TwoSidedIdeal.Quotient.mk (BoundedContinuousFunction.tendstoZeroIdeal B atTop) f :=
  TwoSidedIdeal.Quotient.mkStarAlgHom_apply _ f

theorem mk_surjective : Function.Surjective (mk (B := B)) :=
  TwoSidedIdeal.Quotient.mkStarAlgHom_surjective
    (BoundedContinuousFunction.tendstoZeroIdeal B atTop)

variable (B) in
/-- The canonical quotient projection `(Set.Ici (1 : ℝ) →ᵇ B) →L[ℂ] AsymptoticAlgebra B` as a
contractive continuous `ℂ`-linear map. -/
noncomputable def mkCLM : (Ici (1 : ℝ) →ᵇ B) →L[ℂ] AsymptoticAlgebra B :=
  LinearMap.mkContinuous { toFun := mk, map_add' := map_add mk, map_smul' := map_smul mk } 1
    fun f ↦ by
      simpa only [one_mul, LinearMap.coe_mk, AddHom.coe_mk, mk_apply] using
        TwoSidedIdeal.Quotient.norm_mk_le (BoundedContinuousFunction.tendstoZeroIdeal B atTop) f

@[simp]
theorem mkCLM_apply (f : Ici (1 : ℝ) →ᵇ B) : mkCLM B f = mk f := (rfl)

variable (B) in
theorem mkCLM_surjective : Function.Surjective (mkCLM B) := mk_surjective

@[simp]
theorem mk_eq_zero_iff {f : Ici (1 : ℝ) →ᵇ B} : mk f = 0 ↔ Tendsto f atTop (𝓝 0) := by
  rw [mk_apply]; exact BoundedContinuousFunction.mk_tendstoZeroIdeal_eq_zero_iff

theorem mk_eq_iff {f g : Ici (1 : ℝ) →ᵇ B} :
    mk f = mk g ↔ Tendsto (fun t ↦ f t - g t) atTop (𝓝 0) := by
  rw [mk_apply, mk_apply]; exact BoundedContinuousFunction.mk_tendstoZeroIdeal_eq_iff

theorem norm_mk_eq_limsup (f : Ici (1 : ℝ) →ᵇ B) :
    ‖mk f‖ = limsup (fun t : Ici (1 : ℝ) ↦ ‖f t‖) atTop := by
  rw [mk_apply]; exact BoundedContinuousFunction.norm_mk_tendstoZeroIdeal_Ici_eq_limsup f

end AsymptoticAlgebra

/-- An asymptotic morphism between (possibly nonunital) complex C⋆-algebras `A` and `B` is a family
of maps `φ : Set.Ici (1 : ℝ) → A → B`, continuous in `t` for each fixed `a : A`, that preserves
addition, `ℂ`-scalar multiplication, multiplication, and involution asymptotically as `t → ∞`. No
continuity, linearity, or norm bound at finite `t` is assumed. -/
structure AsymptoticMorphism (A B : Type*) [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] where
  /-- The underlying family of maps `[1, ∞) → A → B`. -/
  toFun : Ici (1 : ℝ) → A → B
  continuous_apply' : ∀ a, Continuous (fun t ↦ toFun t a)
  map_add_tendsto' : ∀ a b,
    Tendsto (fun t ↦ toFun t (a + b) - (toFun t a + toFun t b)) atTop (𝓝 0)
  map_smul_tendsto' : ∀ (c : ℂ) a,
    Tendsto (fun t ↦ toFun t (c • a) - c • toFun t a) atTop (𝓝 0)
  map_mul_tendsto' : ∀ a b,
    Tendsto (fun t ↦ toFun t (a * b) - toFun t a * toFun t b) atTop (𝓝 0)
  map_star_tendsto' : ∀ a,
    Tendsto (fun t ↦ toFun t (star a) - star (toFun t a)) atTop (𝓝 0)

namespace AsymptoticMorphism

section Basic

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]

instance instCoeFun : CoeFun (AsymptoticMorphism A B) (fun _ ↦ Ici (1 : ℝ) → A → B) :=
  ⟨AsymptoticMorphism.toFun⟩

@[simp]
theorem mk_apply (f : Ici (1 : ℝ) → A → B) (hcont hadd hsmul hmul hstar)
    (t : Ici (1 : ℝ)) (a : A) :
    (AsymptoticMorphism.mk f hcont hadd hsmul hmul hstar) t a = f t a := (rfl)

@[ext]
theorem ext {φ ψ : AsymptoticMorphism A B} (h : ∀ t a, φ t a = ψ t a) : φ = ψ := by
  cases φ; cases ψ; simp only [mk.injEq]; ext t a; exact h t a

theorem continuous_apply (φ : AsymptoticMorphism A B) (a : A) : Continuous (fun t ↦ φ t a) :=
  φ.continuous_apply' a

theorem map_add_tendsto (φ : AsymptoticMorphism A B) (a b : A) :
    Tendsto (fun t ↦ φ t (a + b) - (φ t a + φ t b)) atTop (𝓝 0) := φ.map_add_tendsto' a b

theorem map_smul_tendsto (φ : AsymptoticMorphism A B) (c : ℂ) (a : A) :
    Tendsto (fun t ↦ φ t (c • a) - c • φ t a) atTop (𝓝 0) := φ.map_smul_tendsto' c a

theorem map_mul_tendsto (φ : AsymptoticMorphism A B) (a b : A) :
    Tendsto (fun t ↦ φ t (a * b) - φ t a * φ t b) atTop (𝓝 0) := φ.map_mul_tendsto' a b

theorem map_star_tendsto (φ : AsymptoticMorphism A B) (a : A) :
    Tendsto (fun t ↦ φ t (star a) - star (φ t a)) atTop (𝓝 0) := φ.map_star_tendsto' a

theorem map_zero_tendsto (φ : AsymptoticMorphism A B) : Tendsto (fun t ↦ φ t 0) atTop (𝓝 0) := by
  have h : Tendsto (fun t ↦ -φ t 0) atTop (𝓝 0) := by
    simpa only [zero_add, sub_add_cancel_left] using φ.map_add_tendsto 0 0
  simpa only [neg_neg, neg_zero] using h.neg

theorem map_neg_tendsto (φ : AsymptoticMorphism A B) (a : A) :
    Tendsto (fun t ↦ φ t (-a) - -φ t a) atTop (𝓝 0) := by
  simpa only [neg_one_smul] using φ.map_smul_tendsto (-1 : ℂ) a

theorem map_sub_tendsto (φ : AsymptoticMorphism A B) (a b : A) :
    Tendsto (fun t ↦ φ t (a - b) - (φ t a - φ t b)) atTop (𝓝 0) := by
  have h := (φ.map_add_tendsto a (-b)).add (φ.map_neg_tendsto b)
  rw [add_zero] at h
  exact h.congr fun t ↦ by rw [sub_eq_add_neg a b]; abel

instance instZero : Zero (AsymptoticMorphism A B) where
  zero := { toFun := fun _ _ ↦ 0, continuous_apply' := fun _ ↦ continuous_const,
            map_add_tendsto' := fun _ _ ↦ by simp, map_smul_tendsto' := fun _ _ ↦ by simp,
            map_mul_tendsto' := fun _ _ ↦ by simp, map_star_tendsto' := fun _ ↦ by simp }

instance instInhabited : Inhabited (AsymptoticMorphism A B) := ⟨0⟩

@[simp]
theorem zero_apply (t : Ici (1 : ℝ)) (a : A) : (0 : AsymptoticMorphism A B) t a = 0 := (rfl)

/-- The identity asymptotic morphism on `A`, constant in `t`. -/
def id (A : Type*) [NonUnitalCStarAlgebra A] : AsymptoticMorphism A A :=
  { toFun := fun _ a ↦ a, continuous_apply' := fun _ ↦ continuous_const,
    map_add_tendsto' := fun _ _ ↦ by simp, map_smul_tendsto' := fun _ _ ↦ by simp,
    map_mul_tendsto' := fun _ _ ↦ by simp, map_star_tendsto' := fun _ ↦ by simp }

@[simp]
theorem id_apply (t : Ici (1 : ℝ)) (a : A) : AsymptoticMorphism.id A t a = a := (rfl)

/-- Precompose an asymptotic morphism `φ : AsymptoticMorphism B C` with a `⋆`-homomorphism
`f : A →⋆ₙₐ[ℂ] B`. -/
def compStarAlgHom (φ : AsymptoticMorphism B C) (f : A →⋆ₙₐ[ℂ] B) : AsymptoticMorphism A C where
  toFun t a := φ t (f a)
  continuous_apply' a := φ.continuous_apply (f a)
  map_add_tendsto' a b := by simpa only [map_add] using φ.map_add_tendsto (f a) (f b)
  map_smul_tendsto' c a := by simpa only [map_smul] using φ.map_smul_tendsto c (f a)
  map_mul_tendsto' a b := by simpa only [map_mul] using φ.map_mul_tendsto (f a) (f b)
  map_star_tendsto' a := by simpa only [map_star] using φ.map_star_tendsto (f a)

@[simp]
theorem compStarAlgHom_apply (φ : AsymptoticMorphism B C) (f : A →⋆ₙₐ[ℂ] B)
    (t : Ici (1 : ℝ)) (a : A) : φ.compStarAlgHom f t a = φ t (f a) := (rfl)

/-- Postcompose an asymptotic morphism `φ : AsymptoticMorphism A B` with a `⋆`-homomorphism
`g : B →⋆ₙₐ[ℂ] C`. Continuity of `g` is automatic because `⋆`-homomorphisms of C⋆-algebras are
contractive. -/
def postcompStarAlgHom (φ : AsymptoticMorphism A B) (g : B →⋆ₙₐ[ℂ] C) :
    AsymptoticMorphism A C :=
  let hg : Tendsto g (𝓝 0) (𝓝 0) := by simpa only [map_zero] using (map_continuous g).tendsto 0
  { toFun := fun t a ↦ g (φ t a)
    continuous_apply' := fun a ↦ (map_continuous g).comp (φ.continuous_apply a)
    map_add_tendsto' := fun a b ↦ (hg.comp (φ.map_add_tendsto a b)).congr fun _ ↦ by simp
    map_smul_tendsto' := fun c a ↦ (hg.comp (φ.map_smul_tendsto c a)).congr fun _ ↦ by simp
    map_mul_tendsto' := fun a b ↦ (hg.comp (φ.map_mul_tendsto a b)).congr fun _ ↦ by simp
    map_star_tendsto' := fun a ↦
      (hg.comp (φ.map_star_tendsto a)).congr fun _ ↦ by simp [map_star] }

@[simp]
theorem postcompStarAlgHom_apply (φ : AsymptoticMorphism A B) (g : B →⋆ₙₐ[ℂ] C)
    (t : Ici (1 : ℝ)) (a : A) : φ.postcompStarAlgHom g t a = g (φ t a) := (rfl)

/-- Reparameterize an asymptotic morphism along a continuous map `r : C(Set.Ici 1, Set.Ici 1)`
satisfying `Tendsto r atTop atTop`. -/
def reparam (φ : AsymptoticMorphism A B) (r : C(Ici (1 : ℝ), Ici (1 : ℝ)))
    (hr : Tendsto r atTop atTop) : AsymptoticMorphism A B where
  toFun t a := φ (r t) a
  continuous_apply' a := (φ.continuous_apply a).comp r.continuous
  map_add_tendsto' a b := (φ.map_add_tendsto a b).comp hr
  map_smul_tendsto' c a := (φ.map_smul_tendsto c a).comp hr
  map_mul_tendsto' a b := (φ.map_mul_tendsto a b).comp hr
  map_star_tendsto' a := (φ.map_star_tendsto a).comp hr

@[simp]
theorem reparam_apply (φ : AsymptoticMorphism A B) (r : C(Ici (1 : ℝ), Ici (1 : ℝ)))
    (hr : Tendsto r atTop atTop) (t : Ici (1 : ℝ)) (a : A) :
    φ.reparam r hr t a = φ (r t) a := (rfl)

end Basic

section UnitizationAndBoundedness

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- Lift an asymptotic morphism `φ : AsymptoticMorphism A B` to minimal unitizations
`Unitization ℂ A → Unitization ℂ B` by sending `(c, a) ↦ (c, φ t a)`. -/
def unitization (φ : AsymptoticMorphism A B) :
    AsymptoticMorphism (Unitization ℂ A) (Unitization ℂ B) :=
  let hinr : Tendsto ((↑) : B → Unitization ℂ B) (𝓝 0) (𝓝 0) :=
    Unitization.continuous_inr.tendsto' (0 : B) 0 (Unitization.inr_zero ℂ)
  { toFun := fun t x ↦ Unitization.inl x.fst + (φ t x.snd : Unitization ℂ B)
    continuous_apply' := fun x ↦
      continuous_const.add (Unitization.continuous_inr.comp (φ.continuous_apply x.snd))
    map_add_tendsto' := fun x y ↦ (hinr.comp (φ.map_add_tendsto x.snd y.snd)).congr fun _ ↦ by
      simp only [Function.comp_apply, Unitization.fst_add, Unitization.snd_add, Unitization.inl_add,
        Unitization.inr_sub, Unitization.inr_add]
      abel
    map_smul_tendsto' := fun c x ↦ (hinr.comp (φ.map_smul_tendsto c x.snd)).congr fun _ ↦ by
      simp only [Function.comp_apply, Unitization.fst_smul, Unitization.snd_smul, smul_eq_mul,
        ← Unitization.inl_smul, Unitization.inr_sub, Unitization.inr_smul, smul_add]
      abel
    map_mul_tendsto' := fun x y ↦ by
      let u := x.fst • y.snd; let v := y.fst • x.snd; let w := x.snd * y.snd
      have hb : Tendsto (fun t ↦ φ t (u + v + w) -
          (x.fst • φ t y.snd + y.fst • φ t x.snd + φ t x.snd * φ t y.snd)) atTop (𝓝 0) := by
        have hsum := ((((φ.map_add_tendsto (u + v) w).add (φ.map_add_tendsto u v)).add
          (φ.map_smul_tendsto x.fst y.snd)).add (φ.map_smul_tendsto y.fst x.snd)).add
          (φ.map_mul_tendsto x.snd y.snd)
        simp only [add_zero] at hsum
        exact hsum.congr fun _ ↦ by dsimp only [u, v, w]; abel
      refine (hinr.comp hb).congr fun _ ↦ ?_
      ext <;> simp [Unitization.fst_mul, Unitization.snd_mul, u, v, w]
    map_star_tendsto' := fun x ↦ (hinr.comp (φ.map_star_tendsto x.snd)).congr fun _ ↦ by
      simp only [Function.comp_apply, Unitization.fst_star, Unitization.snd_star,
        Unitization.inl_star, Unitization.inr_sub, Unitization.inr_star, star_add]
      abel }

@[simp]
theorem unitization_apply (φ : AsymptoticMorphism A B) (t : Ici (1 : ℝ)) (x : Unitization ℂ A) :
    φ.unitization t x = Unitization.inl x.fst + (φ t x.snd : Unitization ℂ B) := (rfl)

theorem unitization_inr (φ : AsymptoticMorphism A B) (t : Ici (1 : ℝ)) (a : A) :
    φ.unitization t (a : Unitization ℂ A) = (φ t a : Unitization ℂ B) := by
  simp [unitization_apply]

theorem unitization_one_tendsto (φ : AsymptoticMorphism A B) :
    Tendsto (fun t ↦ φ.unitization t 1) atTop (𝓝 1) := by
  have hinr : Tendsto ((↑) : B → Unitization ℂ B) (𝓝 0) (𝓝 0) :=
    Unitization.continuous_inr.tendsto' (0 : B) 0 (Unitization.inr_zero ℂ)
  simpa only [add_zero, Function.comp_apply, unitization_apply, Unitization.fst_one,
    Unitization.inl_one, Unitization.snd_one] using
    (tendsto_const_nhds (x := (1 : Unitization ℂ B))).add (hinr.comp φ.map_zero_tendsto)

/-- For a self-adjoint element `a : A`, the skew-adjoint part `(2⁻¹ : ℝ) • (φ t a - star (φ t a))`
tends to `0` as `t → ∞`. -/
private theorem tendsto_skewAdjointPart_of_isSelfAdjoint (φ : AsymptoticMorphism A B) {a : A}
    (ha : IsSelfAdjoint a) :
    Tendsto (fun t ↦ (skewAdjointPart ℝ (φ t a) : B)) atTop (𝓝 0) := by
  have h := φ.map_star_tendsto a
  rw [ha.star_eq] at h
  simpa only [skewAdjointPart_apply_coe, smul_zero] using h.const_smul (⅟2 : ℝ)

/-- Symmetrizing `φ t a * φ t a + φ t b * φ t b → c` (for self-adjoint `a`, `b`, `c`) via
`TauCeti.selfAdjointPart_mul_self_add_skewAdjointPart_mul_self` cancels the anticommutators between
self-adjoint and skew-adjoint parts identically at every `t`, so subtracting the squared
skew-adjoint errors requires no boundedness assumption on `φ t a` or `φ t b`. -/
private theorem tendsto_selfAdjointPart_mul_self_add_of_isSelfAdjoint
    (φ : AsymptoticMorphism A B) {a b : A} {c : B}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hc : IsSelfAdjoint c)
    (hsum : Tendsto (fun t ↦ φ t a * φ t a + φ t b * φ t b) atTop (𝓝 c)) :
    Tendsto (fun t ↦ (selfAdjointPart ℝ (φ t a) : B) * selfAdjointPart ℝ (φ t a) +
      (selfAdjointPart ℝ (φ t b) : B) * selfAdjointPart ℝ (φ t b)) atTop (𝓝 c) := by
  have hcont : Continuous (fun z : B ↦ (selfAdjointPart ℝ z : B)) := by
    simp only [selfAdjointPart_apply_coe]; fun_prop
  have havg : Tendsto (fun t ↦
      (selfAdjointPart ℝ (φ t a * φ t a + φ t b * φ t b) : B)) atTop (𝓝 c) :=
    (hcont.tendsto' c c (hc.coe_selfAdjointPart_apply ℝ)).comp hsum
  have hsym : Tendsto (fun t ↦
      ((selfAdjointPart ℝ (φ t a) : B) * selfAdjointPart ℝ (φ t a) +
        (skewAdjointPart ℝ (φ t a) : B) * skewAdjointPart ℝ (φ t a)) +
      ((selfAdjointPart ℝ (φ t b) : B) * selfAdjointPart ℝ (φ t b) +
        (skewAdjointPart ℝ (φ t b) : B) * skewAdjointPart ℝ (φ t b))) atTop (𝓝 c) :=
    havg.congr fun t ↦ by
      rw [map_add, AddSubgroup.coe_add,
        ← selfAdjointPart_mul_self_add_skewAdjointPart_mul_self ℝ,
        ← selfAdjointPart_mul_self_add_skewAdjointPart_mul_self ℝ]
  have herr : Tendsto (fun t ↦
      (skewAdjointPart ℝ (φ t a) : B) * skewAdjointPart ℝ (φ t a) +
        (skewAdjointPart ℝ (φ t b) : B) * skewAdjointPart ℝ (φ t b)) atTop (𝓝 0) := by
    have hα := φ.tendsto_skewAdjointPart_of_isSelfAdjoint ha
    have hβ := φ.tendsto_skewAdjointPart_of_isSelfAdjoint hb
    simpa only [mul_zero, add_zero] using (hα.mul hα).add (hβ.mul hβ)
  have hsub := hsym.sub herr
  rw [sub_zero] at hsub
  exact hsub.congr fun _ ↦ by abel

/-- Key step of Blackadar's Proposition 25.1.3: if `φ` is an asymptotic morphism between unital
C⋆-algebras sending `1` asymptotically to `1`, then `t ↦ ‖φ t a‖` is eventually bounded for every
self-adjoint contraction `a`. -/
private theorem exists_eventually_norm_le_of_isSelfAdjoint_le_one
    {A₁ B₁ : Type*} [CStarAlgebra A₁] [CStarAlgebra B₁]
    (φ : AsymptoticMorphism A₁ B₁) (h1 : Tendsto (fun t ↦ φ t 1) atTop (𝓝 1))
    {a : A₁} (ha : IsSelfAdjoint a) (ha_norm : ‖a‖ ≤ 1) :
    ∃ C, ∀ᶠ t in atTop, ‖φ t a‖ ≤ C := by
  -- Step 1: Decompose `a * a + b * b = 1` with `b = √(1 - a²)` so `φ t a² + φ t b² → 1`.
  let _ : PartialOrder A₁ := CStarAlgebra.spectralOrder A₁
  let _ : StarOrderedRing A₁ := CStarAlgebra.spectralOrderedRing A₁
  have ha2_nonneg : 0 ≤ a ^ 2 := by rw [sq]; nth_rw 1 [← ha.star_eq]; exact star_mul_self_nonneg a
  have _ : 0 ≤ 1 - a ^ 2 := by
    rw [sub_nonneg, ← CStarAlgebra.norm_le_one_iff_of_nonneg (a ^ 2) ha2_nonneg, sq,
      ha.norm_mul_self]
    exact pow_le_one₀ (norm_nonneg a) ha_norm
  set b : A₁ := CFC.sqrt (1 - a ^ 2)
  have hb : IsSelfAdjoint b := (CFC.sqrt_nonneg (1 - a ^ 2)).isSelfAdjoint
  have hbb : b * b = 1 - a ^ 2 := CFC.sqrt_mul_sqrt_self (1 - a ^ 2)
  have hab : a * a + b * b = 1 := by rw [hbb, sq, add_sub_cancel]
  have hsum_lim : Tendsto (fun t ↦ φ t a * φ t a + φ t b * φ t b) atTop (𝓝 1) := by
    have hdef : Tendsto (fun t ↦ φ t (a * a + b * b) - (φ t a * φ t a + φ t b * φ t b))
        atTop (𝓝 0) := by
      have h := ((φ.map_add_tendsto (a * a) (b * b)).add (φ.map_mul_tendsto a a)).add
        (φ.map_mul_tendsto b b)
      simp only [add_zero] at h
      exact h.congr fun _ ↦ by abel
    have h1ab : Tendsto (fun t ↦ φ t (a * a + b * b)) atTop (𝓝 1) := by simpa only [hab] using h1
    simpa only [sub_zero, sub_sub_cancel] using h1ab.sub hdef
  -- Step 2: Symmetrize to cancel cross-terms and obtain `(selfAdjointPart)² + (selfAdjointPart)²`.
  have hxy_lim := φ.tendsto_selfAdjointPart_mul_self_add_of_isSelfAdjoint ha hb
    (IsSelfAdjoint.one B₁) hsum_lim
  have hα_zero := φ.tendsto_skewAdjointPart_of_isSelfAdjoint ha
  -- Step 3: Bound `‖selfAdjointPart ℝ (φ t a)‖` via positive squares and recombine `φ t a`.
  obtain ⟨M, hM⟩ := hxy_lim.norm.isBoundedUnder_le.eventually_le
  have hsub : Tendsto (fun t ↦ φ t a - (selfAdjointPart ℝ (φ t a) : B₁)) atTop (𝓝 0) :=
    hα_zero.congr fun t ↦
      (sub_eq_of_eq_add' (StarModule.selfAdjointPart_add_skewAdjointPart ℝ (φ t a)).symm).symm
  refine hsub.exists_eventually_norm_le_of_sub ⟨√M, hM.mono fun t htxy ↦ ?_⟩
  exact (((selfAdjointPart ℝ (φ t a)).property).norm_le_sqrt_norm_mul_self_add
    (selfAdjointPart ℝ (φ t b)).property).trans (Real.sqrt_le_sqrt htxy)

/-- Rescaling any self-adjoint element to a contraction upgrades
`exists_eventually_norm_le_of_isSelfAdjoint_le_one` to all self-adjoint elements when `φ t 1 → 1`.
-/
private theorem exists_eventually_norm_le_of_isSelfAdjoint
    {A₁ B₁ : Type*} [CStarAlgebra A₁] [CStarAlgebra B₁]
    (φ : AsymptoticMorphism A₁ B₁) (h1 : Tendsto (fun t ↦ φ t 1) atTop (𝓝 1))
    {a : A₁} (ha : IsSelfAdjoint a) :
    ∃ C, ∀ᶠ t in atTop, ‖φ t a‖ ≤ C := by
  rcases eq_or_ne ‖a‖ 0 with ha0 | ha0
  · rw [norm_eq_zero] at ha0; subst ha0
    exact φ.map_zero_tendsto.norm.isBoundedUnder_le.eventually_le
  · have hpos : 0 < ‖a‖ := lt_of_le_of_ne (norm_nonneg a) (Ne.symm ha0)
    let a' : A₁ := ((‖a‖⁻¹ : ℝ) : ℂ) • a
    have ha'_sa : IsSelfAdjoint a' := by
      rw [IsSelfAdjoint, star_smul, ha.star_eq, Complex.star_def, Complex.conj_ofReal]
    have ha'_norm : ‖a'‖ ≤ 1 := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le),
        inv_mul_cancel₀ ha0]
    obtain ⟨C₀, hC₀⟩ := φ.exists_eventually_norm_le_of_isSelfAdjoint_le_one h1 ha'_sa ha'_norm
    have hscale : (‖a‖ : ℂ) • a' = a := by
      simp only [a', smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ ha0, Complex.ofReal_one,
        one_smul]
    have hdef : Tendsto (fun t ↦ φ t a - (‖a‖ : ℂ) • φ t a') atTop (𝓝 0) :=
      (φ.map_smul_tendsto (‖a‖ : ℂ) a').congr fun _ ↦ by rw [hscale]
    refine hdef.exists_eventually_norm_le_of_sub ⟨‖a‖ * C₀, hC₀.mono fun t ht ↦ ?_⟩
    rw [norm_smul, Complex.norm_of_nonneg hpos.le]
    exact mul_le_mul_of_nonneg_left ht hpos.le

/-- Every asymptotic morphism `φ : AsymptoticMorphism A B` is eventually bounded in `t` at each
element `a : A`. -/
theorem exists_eventually_norm_le (φ : AsymptoticMorphism A B) (a : A) :
    ∃ C, ∀ᶠ t in atTop, ‖φ t a‖ ≤ C := by
  let ψ := φ.unitization
  let z : Unitization ℂ A := (a : Unitization ℂ A)
  obtain ⟨C₁, hC₁⟩ :=
    ψ.exists_eventually_norm_le_of_isSelfAdjoint φ.unitization_one_tendsto (ℜ z).property
  obtain ⟨C₂, hC₂⟩ :=
    ψ.exists_eventually_norm_le_of_isSelfAdjoint φ.unitization_one_tendsto (ℑ z).property
  have hdef : Tendsto (fun t ↦ ψ t z - (ψ t (ℜ z) + Complex.I • ψ t (ℑ z))) atTop (𝓝 0) := by
    have h := (ψ.map_add_tendsto (ℜ z) (Complex.I • (ℑ z : Unitization ℂ A))).add
      (ψ.map_smul_tendsto Complex.I (ℑ z))
    rw [realPart_add_I_smul_imaginaryPart z, add_zero] at h
    exact h.congr fun _ ↦ by abel
  obtain ⟨C, hC⟩ := hdef.exists_eventually_norm_le_of_sub ⟨C₁ + C₂,
    (hC₁.and hC₂).mono fun t ⟨ht₁, ht₂⟩ ↦ (norm_add_le _ _).trans
      (by rw [norm_smul, Complex.norm_I, one_mul]; exact add_le_add ht₁ ht₂)⟩
  exact ⟨C, hC.mono fun t ht ↦ by simpa only [ψ, z, unitization_inr, Unitization.norm_inr] using ht⟩

/-- For each `a : A`, the trajectory `t ↦ φ t a` of an asymptotic morphism is a bounded continuous
function on `Set.Ici (1 : ℝ)`. -/
noncomputable def toBounded (φ : AsymptoticMorphism A B) (a : A) : Ici (1 : ℝ) →ᵇ B :=
  BoundedContinuousFunction.ofEventuallyBoundedIci (fun t ↦ φ t a)
    (φ.continuous_apply a) (φ.exists_eventually_norm_le a)

@[simp]
theorem toBounded_apply (φ : AsymptoticMorphism A B) (a : A) (t : Ici (1 : ℝ)) :
    φ.toBounded a t = φ t a :=
  BoundedContinuousFunction.ofEventuallyBoundedIci_apply _ _ _ t

@[simp]
theorem coe_toBounded (φ : AsymptoticMorphism A B) (a : A) :
    ⇑(φ.toBounded a) = fun t ↦ φ t a :=
  BoundedContinuousFunction.coe_ofEventuallyBoundedIci _ _ _

/-- The `⋆`-homomorphism `A →⋆ₙₐ[ℂ] AsymptoticAlgebra B` into `C_b([1, ∞), B) ⧸ C₀([1, ∞), B)`
induced by an asymptotic morphism `φ`. -/
noncomputable def toAsymptoticHom (φ : AsymptoticMorphism A B) :
    A →⋆ₙₐ[ℂ] AsymptoticAlgebra B where
  toFun a := AsymptoticAlgebra.mk (φ.toBounded a)
  map_smul' c a := by
    rw [← map_smul, AsymptoticAlgebra.mk_eq_iff]
    exact (φ.map_smul_tendsto c a).congr fun _ ↦ by simp [toBounded_apply]
  map_zero' := by rw [AsymptoticAlgebra.mk_eq_zero_iff, coe_toBounded]; exact φ.map_zero_tendsto
  map_add' a b := by
    rw [← map_add, AsymptoticAlgebra.mk_eq_iff]
    exact (φ.map_add_tendsto a b).congr fun _ ↦ by simp [toBounded_apply]
  map_mul' a b := by
    rw [← map_mul, AsymptoticAlgebra.mk_eq_iff]
    exact (φ.map_mul_tendsto a b).congr fun _ ↦ by simp [toBounded_apply]
  map_star' a := by
    rw [← map_star, AsymptoticAlgebra.mk_eq_iff]
    exact (φ.map_star_tendsto a).congr fun _ ↦ by simp [toBounded_apply]

@[simp]
theorem toAsymptoticHom_apply (φ : AsymptoticMorphism A B) (a : A) :
    φ.toAsymptoticHom a = AsymptoticAlgebra.mk (φ.toBounded a) := (rfl)

/-- The quotient norm of `φ.toAsymptoticHom a` in `AsymptoticAlgebra B` equals
`limsup (fun t ↦ ‖φ t a‖) atTop`. -/
theorem norm_toAsymptoticHom_eq_limsup (φ : AsymptoticMorphism A B) (a : A) :
    ‖φ.toAsymptoticHom a‖ = limsup (fun t : Ici (1 : ℝ) ↦ ‖φ t a‖) atTop := by
  rw [toAsymptoticHom_apply, AsymptoticAlgebra.norm_mk_eq_limsup]; simp only [toBounded_apply]

/-- **Asymptotic contractivity** (Blackadar, Proposition 25.1.3): for every asymptotic morphism
`φ : AsymptoticMorphism A B` and every `a : A`, `limsup (fun t ↦ ‖φ t a‖) atTop ≤ ‖a‖`. -/
theorem limsup_norm_le (φ : AsymptoticMorphism A B) (a : A) :
    limsup (fun t : Ici (1 : ℝ) ↦ ‖φ t a‖) atTop ≤ ‖a‖ := by
  rw [← φ.norm_toAsymptoticHom_eq_limsup a]
  exact NonUnitalStarAlgHom.norm_apply_le φ.toAsymptoticHom a

/-- Pointwise eventual form of asymptotic contractivity: for every `a : A` and `ε > 0`, eventually
`‖φ t a‖ < ‖a‖ + ε`. -/
theorem eventually_norm_lt_add (φ : AsymptoticMorphism A B) (a : A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : Ici (1 : ℝ) in atTop, ‖φ t a‖ < ‖a‖ + ε := by
  refine eventually_lt_of_limsup_lt ((φ.limsup_norm_le a).trans_lt (lt_add_of_pos_right ‖a‖ hε))
    ⟨‖φ.toBounded a‖, eventually_map.mpr (Eventually.of_forall fun t ↦ ?_)⟩
  simpa only [toBounded_apply] using (φ.toBounded a).norm_coe_le_norm t

end UnitizationAndBoundedness

section Equivalence

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- Two asymptotic morphisms `φ, ψ : AsymptoticMorphism A B` are *asymptotically equivalent* if
`φ t a - ψ t a → 0` as `t → ∞` for every `a : A`. -/
def IsAsymptoticallyEquivalent (φ ψ : AsymptoticMorphism A B) : Prop :=
  ∀ a, Tendsto (fun t ↦ φ t a - ψ t a) atTop (𝓝 0)

theorem isAsymptoticallyEquivalent_def {φ ψ : AsymptoticMorphism A B} :
    φ.IsAsymptoticallyEquivalent ψ ↔ ∀ a, Tendsto (fun t ↦ φ t a - ψ t a) atTop (𝓝 0) := Iff.rfl

theorem IsAsymptoticallyEquivalent.tendsto {φ ψ : AsymptoticMorphism A B}
    (h : φ.IsAsymptoticallyEquivalent ψ) (a : A) :
    Tendsto (fun t ↦ φ t a - ψ t a) atTop (𝓝 0) := h a

@[refl]
theorem IsAsymptoticallyEquivalent.refl (φ : AsymptoticMorphism A B) :
    φ.IsAsymptoticallyEquivalent φ := fun _ ↦ by simp

@[symm]
theorem IsAsymptoticallyEquivalent.symm {φ ψ : AsymptoticMorphism A B}
    (h : φ.IsAsymptoticallyEquivalent ψ) : ψ.IsAsymptoticallyEquivalent φ :=
  fun a ↦ by simpa only [neg_sub, neg_zero] using (h a).neg

@[trans]
theorem IsAsymptoticallyEquivalent.trans {φ ψ χ : AsymptoticMorphism A B}
    (h₁ : φ.IsAsymptoticallyEquivalent ψ) (h₂ : ψ.IsAsymptoticallyEquivalent χ) :
    φ.IsAsymptoticallyEquivalent χ :=
  fun a ↦ by simpa only [sub_add_sub_cancel, add_zero] using (h₁ a).add (h₂ a)

/-- The setoid of asymptotic equivalence on `AsymptoticMorphism A B`. -/
def isAsymptoticallyEquivalentSetoid (A B : Type*) [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B] : Setoid (AsymptoticMorphism A B) :=
  ⟨IsAsymptoticallyEquivalent,
    ⟨IsAsymptoticallyEquivalent.refl, IsAsymptoticallyEquivalent.symm,
      IsAsymptoticallyEquivalent.trans⟩⟩

/-- Two asymptotic morphisms are asymptotically equivalent if and only if they induce the same
`⋆`-homomorphism `A →⋆ₙₐ[ℂ] AsymptoticAlgebra B`. -/
theorem isAsymptoticallyEquivalent_iff_toAsymptoticHom_eq {φ ψ : AsymptoticMorphism A B} :
    φ.IsAsymptoticallyEquivalent ψ ↔ φ.toAsymptoticHom = ψ.toAsymptoticHom := by
  rw [DFunLike.ext_iff, IsAsymptoticallyEquivalent]
  exact forall_congr' fun _ ↦ by
    rw [toAsymptoticHom_apply, toAsymptoticHom_apply, AsymptoticAlgebra.mk_eq_iff]
    simp only [toBounded_apply]

/-- Construct an asymptotic morphism `A → B` from any family of bounded continuous lifts
`s : A → (Set.Ici (1 : ℝ) →ᵇ B)` of a `⋆`-homomorphism `Φ : A →⋆ₙₐ[ℂ] AsymptoticAlgebra B`. -/
def ofAsymptoticHomSection {Φ : A →⋆ₙₐ[ℂ] AsymptoticAlgebra B}
    (s : A → (Ici (1 : ℝ) →ᵇ B)) (hs : ∀ a, AsymptoticAlgebra.mk (s a) = Φ a) :
    AsymptoticMorphism A B where
  toFun t a := s a t
  continuous_apply' a := (s a).continuous
  map_add_tendsto' a b := by
    have h : AsymptoticAlgebra.mk (s (a + b)) = AsymptoticAlgebra.mk (s a + s b) := by
      rw [map_add, hs, hs, hs, map_add]
    simpa using AsymptoticAlgebra.mk_eq_iff.mp h
  map_smul_tendsto' c a := by
    have h : AsymptoticAlgebra.mk (s (c • a)) = AsymptoticAlgebra.mk (c • s a) := by
      rw [map_smul, hs, hs, map_smul]
    simpa using AsymptoticAlgebra.mk_eq_iff.mp h
  map_mul_tendsto' a b := by
    have h : AsymptoticAlgebra.mk (s (a * b)) = AsymptoticAlgebra.mk (s a * s b) := by
      rw [map_mul, hs, hs, hs, map_mul]
    simpa using AsymptoticAlgebra.mk_eq_iff.mp h
  map_star_tendsto' a := by
    have h : AsymptoticAlgebra.mk (s (star a)) = AsymptoticAlgebra.mk (star (s a)) := by
      rw [map_star, hs, hs, map_star]
    simpa using AsymptoticAlgebra.mk_eq_iff.mp h

@[simp]
theorem ofAsymptoticHomSection_apply {Φ : A →⋆ₙₐ[ℂ] AsymptoticAlgebra B}
    (s : A → (Ici (1 : ℝ) →ᵇ B)) (hs : ∀ a, AsymptoticAlgebra.mk (s a) = Φ a)
    (t : Ici (1 : ℝ)) (a : A) : ofAsymptoticHomSection s hs t a = s a t := (rfl)

@[simp]
theorem toBounded_ofAsymptoticHomSection {Φ : A →⋆ₙₐ[ℂ] AsymptoticAlgebra B}
    (s : A → (Ici (1 : ℝ) →ᵇ B)) (hs : ∀ a, AsymptoticAlgebra.mk (s a) = Φ a) (a : A) :
    (ofAsymptoticHomSection s hs).toBounded a = s a := by
  ext t; rw [toBounded_apply, ofAsymptoticHomSection_apply]

@[simp]
theorem toAsymptoticHom_ofAsymptoticHomSection {Φ : A →⋆ₙₐ[ℂ] AsymptoticAlgebra B}
    (s : A → (Ici (1 : ℝ) →ᵇ B)) (hs : ∀ a, AsymptoticAlgebra.mk (s a) = Φ a) :
    (ofAsymptoticHomSection s hs).toAsymptoticHom = Φ := by
  ext a; simp [toAsymptoticHom_apply, hs]

/-- **Blackadar, Proposition 25.1.4(a)**: equivalence classes of asymptotic morphisms `A → B` are
in canonical bijection with `⋆`-homomorphisms `A →⋆ₙₐ[ℂ] AsymptoticAlgebra B`. -/
noncomputable def quotientEquivAsymptoticHom (A B : Type*) [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B] :
    Quotient (isAsymptoticallyEquivalentSetoid A B) ≃ (A →⋆ₙₐ[ℂ] AsymptoticAlgebra B) where
  toFun := Quotient.lift toAsymptoticHom fun _ _ h ↦
    isAsymptoticallyEquivalent_iff_toAsymptoticHom_eq.mp h
  invFun Φ := Quotient.mk (isAsymptoticallyEquivalentSetoid A B)
    (ofAsymptoticHomSection (fun a ↦ Function.surjInv AsymptoticAlgebra.mk_surjective (Φ a))
      fun a ↦ Function.surjInv_eq AsymptoticAlgebra.mk_surjective (Φ a))
  left_inv q := by
    obtain ⟨φ, rfl⟩ := Quotient.exists_rep q
    exact Quotient.sound (isAsymptoticallyEquivalent_iff_toAsymptoticHom_eq.mpr
      (toAsymptoticHom_ofAsymptoticHomSection _ _))
  right_inv _ := toAsymptoticHom_ofAsymptoticHomSection _ _

@[simp]
theorem quotientEquivAsymptoticHom_mk (φ : AsymptoticMorphism A B) :
    quotientEquivAsymptoticHom A B (Quotient.mk (isAsymptoticallyEquivalentSetoid A B) φ) =
      φ.toAsymptoticHom := (rfl)

end Equivalence

end AsymptoticMorphism

end TauCeti

namespace NonUnitalStarAlgHom

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- View a `⋆`-homomorphism `f : A →⋆ₙₐ[ℂ] B` as a constant asymptotic morphism. -/
def toAsymptoticMorphism (f : A →⋆ₙₐ[ℂ] B) : TauCeti.AsymptoticMorphism A B :=
  { toFun := fun _ a ↦ f a, continuous_apply' := fun _ ↦ continuous_const,
    map_add_tendsto' := fun _ _ ↦ by simp [map_add],
    map_smul_tendsto' := fun _ _ ↦ by simp [map_smul],
    map_mul_tendsto' := fun _ _ ↦ by simp [map_mul],
    map_star_tendsto' := fun _ ↦ by simp [map_star] }

@[simp]
theorem toAsymptoticMorphism_apply (f : A →⋆ₙₐ[ℂ] B) (t : Ici (1 : ℝ)) (a : A) :
    f.toAsymptoticMorphism t a = f a := (rfl)

/-- Rescaled perturbation `(t, a) ↦ (1 + t⁻¹) • f a` of a `⋆`-homomorphism `f : A →⋆ₙₐ[ℂ] B`:
whenever `p : A` is a projection (`p * p = p`) with `f p ≠ 0`, for every finite `t ≥ 1` the map
`a ↦ (1 + t⁻¹) • f a` fails to be multiplicative at `p` (`(1 + t⁻¹)² ≠ 1 + t⁻¹`), yet the family
is an asymptotic morphism asymptotically equivalent to `f.toAsymptoticMorphism`. -/
noncomputable def rescaledAsymptoticMorphism (f : A →⋆ₙₐ[ℂ] B) :
    TauCeti.AsymptoticMorphism A B where
  toFun t a := ((1 : ℝ) + (t : ℝ)⁻¹) • f a
  continuous_apply' _ :=
    (continuous_const.add
      (continuous_subtypeVal.inv₀ fun t ↦ (zero_lt_one.trans_le t.property).ne')).smul
      continuous_const
  map_add_tendsto' _ _ := by simp [map_add, smul_add]
  map_smul_tendsto' c _ := by simp [map_smul, smul_comm ((1 : ℝ) + (_ : ℝ)⁻¹) c]
  map_mul_tendsto' a b := by
    have hinv : Tendsto (fun t : Ici (1 : ℝ) ↦ (t : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_comp_val_Ici_atTop.mpr tendsto_inv_atTop_zero
    have hc : Tendsto (fun t : Ici (1 : ℝ) ↦ (1 : ℝ) + (t : ℝ)⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hinv
    have hcoeff : Tendsto (fun t : Ici (1 : ℝ) ↦
        (1 + (t : ℝ)⁻¹) - (1 + (t : ℝ)⁻¹) * (1 + (t : ℝ)⁻¹)) atTop (𝓝 0) := by
      simpa using hc.sub (hc.mul hc)
    have hsmul : Tendsto (fun t : Ici (1 : ℝ) ↦
        ((1 + (t : ℝ)⁻¹) - (1 + (t : ℝ)⁻¹) * (1 + (t : ℝ)⁻¹)) • (f a * f b)) atTop (𝓝 0) := by
      simpa only [zero_smul] using hcoeff.smul_const (f a * f b)
    refine hsmul.congr fun _ ↦ ?_
    rw [map_mul, sub_smul, smul_mul_smul_comm, mul_smul]
  map_star_tendsto' _ := by simp [map_star, star_smul]

@[simp]
theorem rescaledAsymptoticMorphism_apply (f : A →⋆ₙₐ[ℂ] B) (t : Ici (1 : ℝ)) (a : A) :
    f.rescaledAsymptoticMorphism t a = ((1 : ℝ) + (t : ℝ)⁻¹) • f a := (rfl)

/-- The rescaled family `(1 + t⁻¹) • f a` is asymptotically equivalent to `f.toAsymptoticMorphism`.
-/
theorem isAsymptoticallyEquivalent_rescaledAsymptoticMorphism (f : A →⋆ₙₐ[ℂ] B) :
    f.rescaledAsymptoticMorphism.IsAsymptoticallyEquivalent f.toAsymptoticMorphism := fun a ↦ by
  have h : Tendsto (fun t : Ici (1 : ℝ) ↦ (t : ℝ)⁻¹ • f a) atTop (𝓝 0) := by
    have hinv : Tendsto (fun t : Ici (1 : ℝ) ↦ (t : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_comp_val_Ici_atTop.mpr tendsto_inv_atTop_zero
    simpa only [zero_smul] using hinv.smul_const (f a)
  exact h.congr fun _ ↦ by
    simp [rescaledAsymptoticMorphism_apply, toAsymptoticMorphism_apply, add_smul]

end NonUnitalStarAlgHom
