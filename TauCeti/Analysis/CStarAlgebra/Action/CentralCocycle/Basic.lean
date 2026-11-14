/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import TauCeti.Analysis.CStarAlgebra.Action.Multiplier

/-!
# Normalized continuous central multiplier 2-cocycles

For a point-norm continuous action `α` of a topological group `G` on a possibly nonunital complex
C⋆-algebra `A`, a *normalized continuous central `α`-cocycle* (`CentralCocycle α`) is a map
`ω : G → G → unitary 𝓜(ℂ, A)` taking values in the unitary center of the multiplier algebra
`𝓜(ℂ, A)` and satisfying

* `ω 1 s = 1` and `ω s 1 = 1`,
* `α.multiplier r (ω s t) * ω r (s * t) = ω r s * ω (r * s, t)`,
* norm continuity of `(s, t) ↦ (ω s t : 𝓜(ℂ, A)).fst a` (equivalently `.snd a`, by centrality)
  for every `a : A`.

Centrality allows `α` to remain an honest group action on `A`, rather than a Busby–Smith twisted
action whose automorphisms compose only up to inner automorphisms. Because unitary multipliers act
isometrically on `A`, pointwise strict continuity upgrades automatically to joint norm continuity
of `(x ↦ (ω (r x) (s x) : 𝓜(ℂ, A)).fst (f x))` for continuous `r, s : X → G` and `f : X → A`,
and likewise for the adjoints `star (ω (r x) (s x) : 𝓜(ℂ, A))`. No unitality of `A` (including
`A = 0`), local compactness, separability, or second countability is assumed.

Normalized continuous central `α`-cocycles form an abelian group (`CommGroup (CentralCocycle α)`)
under pointwise multiplication, pull back along continuous group homomorphisms (`comp`), transport
along star-algebra equivalences (`conjugate`), and include normalized continuous circle-valued
scalar 2-cocycles (`ofCircle`).

## Main definitions

* `TauCeti.CStarAction.CentralCocycle`: normalized continuous central multiplier 2-cocycles of `α`.
* `TauCeti.CStarAction.CentralCocycle.ofForallFstEqSnd`: constructor checking centrality and the
  cocycle identity on `A`.
* `TauCeti.CStarAction.CentralCocycle.comp`: pullback homomorphism along a `ContinuousMonoidHom`.
* `TauCeti.CStarAction.CentralCocycle.conjugate`: multiplicative equivalence transporting cocycles
  along `e : A ≃⋆ₐ[ℂ] B`.
* `TauCeti.CStarAction.CentralCocycle.ofCircle`: embedding of normalized continuous `Circle`-valued
  2-cocycles into `CentralCocycle α`.

## References

* J. Packer and I. Raeburn, *Twisted crossed products of C*-algebras*, Math. Proc. Cambridge
  Philos. Soc. 106 (1989), 293–311, Section 2.
* D. P. Williams, *Crossed Products of C*-Algebras*, Mathematical Surveys and Monographs 134,
  American Mathematical Society, 2007, Chapter 2.
-/

public section

noncomputable section

open scoped MultiplierAlgebra

namespace TauCeti.CStarAction

variable {G A : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]

/-- A normalized continuous central 2-cocycle for a C⋆-action `α`, valued in the unitary center of
the multiplier algebra `𝓜(ℂ, A)`. Strict continuity is expressed via the left multiplier action on
`A`; centrality implies the corresponding right-action continuity (`continuous_snd`). -/
structure CentralCocycle (α : CStarAction G A) where
  /-- The unitary multiplier assigned to a pair of group elements. -/
  toFun : G → G → unitary 𝓜(ℂ, A)
  /-- Every value commutes with all multipliers in `𝓜(ℂ, A)`. -/
  commute' : ∀ s t (m : 𝓜(ℂ, A)), Commute (toFun s t : 𝓜(ℂ, A)) m
  /-- Normalization at the identity on the left. -/
  map_one_left' : ∀ s, toFun 1 s = 1
  /-- Normalization at the identity on the right. -/
  map_one_right' : ∀ s, toFun s 1 = 1
  /-- The 2-cocycle law `α.multiplier r (ω(s, t)) * ω(r, s * t) = ω(r, s) * ω(r * s, t)`. -/
  mul_cocycle' : ∀ r s t,
    α.multiplier r (toFun s t : 𝓜(ℂ, A)) * (toFun r (s * t) : 𝓜(ℂ, A)) =
      (toFun r s : 𝓜(ℂ, A)) * (toFun (r * s) t : 𝓜(ℂ, A))
  /-- Joint strict continuity of `(s, t) ↦ ω(s, t) a` for each `a : A`. -/
  continuous_fst' : ∀ a : A, Continuous fun q : G × G => (toFun q.1 q.2 : 𝓜(ℂ, A)).fst a

namespace CentralCocycle

variable {α : CStarAction G A}

instance : CoeFun (CentralCocycle α) (fun _ => G → G → unitary 𝓜(ℂ, A)) where
  coe := toFun

@[simp]
theorem mk_apply (f : G → G → unitary 𝓜(ℂ, A)) (hc h1l h1r hcoc hcont) (s t : G) :
    (mk f hc h1l h1r hcoc hcont : CentralCocycle α) s t = f s t :=
  (rfl)

/-- Two central cocycles are equal if they agree on all pairs of group elements. -/
@[ext]
theorem ext {ω₁ ω₂ : CentralCocycle α} (h : ∀ s t, ω₁ s t = ω₂ s t) : ω₁ = ω₂ := by
  have h' : ω₁.toFun = ω₂.toFun := funext fun s => funext fun t => h s t
  cases ω₁
  cases ω₂
  congr

/-- Two central cocycles are equal if their coerced multipliers agree everywhere. -/
theorem ext_coe {ω₁ ω₂ : CentralCocycle α}
    (h : ∀ s t, (ω₁ s t : 𝓜(ℂ, A)) = (ω₂ s t : 𝓜(ℂ, A))) : ω₁ = ω₂ :=
  ext fun s t => Subtype.ext (h s t)

/-- Two central cocycles are equal if their left actions on `A` agree everywhere. -/
theorem ext_fst {ω₁ ω₂ : CentralCocycle α}
    (h : ∀ s t (a : A), (ω₁ s t : 𝓜(ℂ, A)).fst a = (ω₂ s t : 𝓜(ℂ, A)).fst a) : ω₁ = ω₂ :=
  ext_coe fun s t => DoubleCentralizer.ext_fst (h s t)

/-- Construct a `CentralCocycle` by checking centrality and the cocycle identity on `A`. -/
def ofForallFstEqSnd (u : G → G → unitary 𝓜(ℂ, A))
    (hcent : ∀ s t (a : A), (u s t : 𝓜(ℂ, A)).fst a = (u s t : 𝓜(ℂ, A)).snd a)
    (h1l : ∀ s, u 1 s = 1) (h1r : ∀ s, u s 1 = 1)
    (hcoc : ∀ r s t (a : A),
      α r ((u s t : 𝓜(ℂ, A)).fst (α r⁻¹ ((u r (s * t) : 𝓜(ℂ, A)).fst a))) =
        (u r s : 𝓜(ℂ, A)).fst ((u (r * s) t : 𝓜(ℂ, A)).fst a))
    (hcont : ∀ a : A, Continuous fun q : G × G => (u q.1 q.2 : 𝓜(ℂ, A)).fst a) :
    CentralCocycle α where
  toFun := u
  commute' s t := DoubleCentralizer.forall_commute_iff_forall_fst_eq_snd.2 (hcent s t)
  map_one_left' := h1l
  map_one_right' := h1r
  mul_cocycle' r s t := DoubleCentralizer.ext_fst fun a => by simpa using hcoc r s t a
  continuous_fst' := hcont

@[simp]
theorem ofForallFstEqSnd_apply (u : G → G → unitary 𝓜(ℂ, A))
    (hcent h1l h1r hcoc hcont) (s t : G) :
    ofForallFstEqSnd (α := α) u hcent h1l h1r hcoc hcont s t = u s t :=
  (rfl)

/-! ### Centrality, normalization, and cocycle identities -/

/-- Every value of a central cocycle commutes with every multiplier. -/
theorem commute (ω : CentralCocycle α) (s t : G) (m : 𝓜(ℂ, A)) :
    Commute (ω s t : 𝓜(ℂ, A)) m :=
  ω.commute' s t m

/-- The adjoint of every value of a central cocycle commutes with every multiplier. -/
theorem commute_star (ω : CentralCocycle α) (s t : G) (m : 𝓜(ℂ, A)) :
    Commute (star (ω s t : 𝓜(ℂ, A))) m := by
  rw [Commute, SemiconjBy]
  calc star (ω s t : 𝓜(ℂ, A)) * m = star (star m * (ω s t : 𝓜(ℂ, A))) := by simp
    _ = star ((ω s t : 𝓜(ℂ, A)) * star m) := by rw [(ω.commute s t (star m)).eq]
    _ = m * star (ω s t : 𝓜(ℂ, A)) := by simp

/-- Every value of a central cocycle lies in the center of `𝓜(ℂ, A)`. -/
theorem mem_center (ω : CentralCocycle α) (s t : G) :
    (ω s t : 𝓜(ℂ, A)) ∈ Subalgebra.center ℂ 𝓜(ℂ, A) :=
  Subalgebra.mem_center_iff.2 fun m => (ω.commute s t m).symm

/-- Because `ω s t` is central, its right and left centralizers agree on `A`. -/
theorem snd_eq_fst (ω : CentralCocycle α) (s t : G) (a : A) :
    (ω s t : 𝓜(ℂ, A)).snd a = (ω s t : 𝓜(ℂ, A)).fst a :=
  (DoubleCentralizer.forall_commute_iff_forall_fst_eq_snd.1 (ω.commute s t) a).symm

/-- Because `star (ω s t)` is central, its right and left centralizers agree on `A`. -/
theorem star_snd_eq_star_fst (ω : CentralCocycle α) (s t : G) (a : A) :
    (star (ω s t : 𝓜(ℂ, A))).snd a = (star (ω s t : 𝓜(ℂ, A))).fst a :=
  (DoubleCentralizer.forall_commute_iff_forall_fst_eq_snd.1 (ω.commute_star s t) a).symm

@[simp]
theorem map_one_left (ω : CentralCocycle α) (s : G) : ω 1 s = 1 :=
  ω.map_one_left' s

@[simp]
theorem map_one_right (ω : CentralCocycle α) (s : G) : ω s 1 = 1 :=
  ω.map_one_right' s

/-- The 2-cocycle law in the multiplier algebra `𝓜(ℂ, A)`. -/
theorem mul_cocycle (ω : CentralCocycle α) (r s t : G) :
    α.multiplier r (ω s t : 𝓜(ℂ, A)) * (ω r (s * t) : 𝓜(ℂ, A)) =
      (ω r s : 𝓜(ℂ, A)) * (ω (r * s) t : 𝓜(ℂ, A)) :=
  ω.mul_cocycle' r s t

/-- The 2-cocycle law evaluated via left multiplier actions on `A`. -/
theorem fst_cocycle (ω : CentralCocycle α) (r s t : G) (a : A) :
    α r ((ω s t : 𝓜(ℂ, A)).fst (α r⁻¹ ((ω r (s * t) : 𝓜(ℂ, A)).fst a))) =
      (ω r s : 𝓜(ℂ, A)).fst ((ω (r * s) t : 𝓜(ℂ, A)).fst a) := by
  simpa using congrArg (fun m : 𝓜(ℂ, A) => m.fst a) (ω.mul_cocycle r s t)

/-- The 2-cocycle law evaluated via right multiplier actions on `A`. -/
theorem snd_cocycle (ω : CentralCocycle α) (r s t : G) (a : A) :
    (ω r (s * t) : 𝓜(ℂ, A)).snd (α r ((ω s t : 𝓜(ℂ, A)).snd (α r⁻¹ a))) =
      (ω (r * s) t : 𝓜(ℂ, A)).snd ((ω r s : 𝓜(ℂ, A)).snd a) := by
  simpa using congrArg (fun m : 𝓜(ℂ, A) => m.snd a) (ω.mul_cocycle r s t)

/-- Evaluating the cocycle identity at `(s, s⁻¹, s)` gives `α.multiplier s (ω s⁻¹ s) = ω s s⁻¹`. -/
theorem multiplier_apply_inv_mul_self (ω : CentralCocycle α) (s : G) :
    α.multiplier s (ω s⁻¹ s : 𝓜(ℂ, A)) = (ω s s⁻¹ : 𝓜(ℂ, A)) := by
  simpa using ω.mul_cocycle s s⁻¹ s

/-- Inverse form of `multiplier_apply_inv_mul_self`: `α.multiplier s⁻¹ (ω s s⁻¹) = ω s⁻¹ s`. -/
theorem multiplier_inv_apply_mul_inv (ω : CentralCocycle α) (s : G) :
    α.multiplier s⁻¹ (ω s s⁻¹ : 𝓜(ℂ, A)) = (ω s⁻¹ s : 𝓜(ℂ, A)) := by
  simpa using ω.multiplier_apply_inv_mul_self s⁻¹

/-- Adjoint form of `multiplier_apply_inv_mul_self`. -/
theorem multiplier_star_apply_inv_mul_self (ω : CentralCocycle α) (s : G) :
    α.multiplier s (star (ω s⁻¹ s : 𝓜(ℂ, A))) = star (ω s s⁻¹ : 𝓜(ℂ, A)) := by
  rw [map_star, ω.multiplier_apply_inv_mul_self]

/-- Adjoint cocycle identity at `(s, t, t⁻¹)`:
`star (ω s t) = α.multiplier s (star (ω t t⁻¹)) * ω (s * t) t⁻¹`. -/
theorem star_eq_multiplier_star_mul (ω : CentralCocycle α) (s t : G) :
    star (ω s t : 𝓜(ℂ, A)) =
      α.multiplier s (star (ω t t⁻¹ : 𝓜(ℂ, A))) * (ω (s * t) t⁻¹ : 𝓜(ℂ, A)) := by
  have h2 : (ω s t : 𝓜(ℂ, A)) * (ω (s * t) t⁻¹ : 𝓜(ℂ, A)) =
      α.multiplier s (ω t t⁻¹ : 𝓜(ℂ, A)) := by
    simpa using (ω.mul_cocycle s t t⁻¹).symm
  calc star (ω s t : 𝓜(ℂ, A))
      = star (ω s t : 𝓜(ℂ, A)) *
          (α.multiplier s (star (ω t t⁻¹ : 𝓜(ℂ, A))) *
            α.multiplier s (ω t t⁻¹ : 𝓜(ℂ, A))) := by
        rw [← map_mul, (Unitary.mem_iff.mp (ω t t⁻¹).prop).1, map_one, mul_one]
    _ = star (ω s t : 𝓜(ℂ, A)) *
          (α.multiplier s (star (ω t t⁻¹ : 𝓜(ℂ, A))) *
            ((ω s t : 𝓜(ℂ, A)) * (ω (s * t) t⁻¹ : 𝓜(ℂ, A)))) := by
        rw [h2]
    _ = (star (ω s t : 𝓜(ℂ, A)) * (ω s t : 𝓜(ℂ, A))) *
          (α.multiplier s (star (ω t t⁻¹ : 𝓜(ℂ, A))) * (ω (s * t) t⁻¹ : 𝓜(ℂ, A))) := by
        rw [← mul_assoc (α.multiplier s _), ← (ω.commute s t _).eq]
        simp only [mul_assoc]
    _ = α.multiplier s (star (ω t t⁻¹ : 𝓜(ℂ, A))) * (ω (s * t) t⁻¹ : 𝓜(ℂ, A)) := by
        rw [(Unitary.mem_iff.mp (ω s t).prop).1, one_mul]

/-! ### Strict and joint continuity -/

/-- Strict left continuity of `(s, t) ↦ (ω s t).fst a`. -/
theorem continuous_fst (ω : CentralCocycle α) (a : A) :
    Continuous fun q : G × G => (ω q.1 q.2 : 𝓜(ℂ, A)).fst a :=
  ω.continuous_fst' a

/-- Strict right continuity of `(s, t) ↦ (ω s t).snd a`. -/
theorem continuous_snd (ω : CentralCocycle α) (a : A) :
    Continuous fun q : G × G => (ω q.1 q.2 : 𝓜(ℂ, A)).snd a := by
  simp_rw [ω.snd_eq_fst]
  exact ω.continuous_fst a

/-- Strict left continuity of the adjoint `(s, t) ↦ (star (ω s t)).fst a`. -/
theorem continuous_star_fst (ω : CentralCocycle α) (a : A) :
    Continuous fun q : G × G => (star (ω q.1 q.2 : 𝓜(ℂ, A))).fst a := by
  simp_rw [DoubleCentralizer.star_fst]
  exact (ω.continuous_snd (star a)).star

/-- Strict right continuity of the adjoint `(s, t) ↦ (star (ω s t)).snd a`. -/
theorem continuous_star_snd (ω : CentralCocycle α) (a : A) :
    Continuous fun q : G × G => (star (ω q.1 q.2 : 𝓜(ℂ, A))).snd a := by
  simp_rw [DoubleCentralizer.star_snd]
  exact (ω.continuous_fst (star a)).star

section JointContinuity

variable {X : Type*} [TopologicalSpace X] {r s : X → G} {f : X → A}

/-- Joint norm continuity of `x ↦ (ω (r x) (s x)).fst (f x)` for continuous `r, s, f`. -/
@[fun_prop]
theorem continuous_fst_apply (ω : CentralCocycle α)
    (hr : Continuous r) (hs : Continuous s) (hf : Continuous f) :
    Continuous fun x => (ω (r x) (s x) : 𝓜(ℂ, A)).fst (f x) :=
  DoubleCentralizer.continuous_fst_apply_of_norm_le
    (fun a => (ω.continuous_fst a).comp (hr.prodMk hs))
    (fun _ => ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by simp) hf

/-- Joint norm continuity of `x ↦ (ω (r x) (s x)).snd (f x)` for continuous `r, s, f`. -/
@[fun_prop]
theorem continuous_snd_apply (ω : CentralCocycle α)
    (hr : Continuous r) (hs : Continuous s) (hf : Continuous f) :
    Continuous fun x => (ω (r x) (s x) : 𝓜(ℂ, A)).snd (f x) := by
  simp_rw [ω.snd_eq_fst]
  exact ω.continuous_fst_apply hr hs hf

/-- Joint norm continuity of `x ↦ (star (ω (r x) (s x))).fst (f x)` for continuous `r, s, f`. -/
@[fun_prop]
theorem continuous_star_fst_apply (ω : CentralCocycle α)
    (hr : Continuous r) (hs : Continuous s) (hf : Continuous f) :
    Continuous fun x => (star (ω (r x) (s x) : 𝓜(ℂ, A))).fst (f x) := by
  simp_rw [DoubleCentralizer.star_fst]
  exact (ω.continuous_snd_apply hr hs hf.star).star

/-- Joint norm continuity of `x ↦ (star (ω (r x) (s x))).snd (f x)` for continuous `r, s, f`. -/
@[fun_prop]
theorem continuous_star_snd_apply (ω : CentralCocycle α)
    (hr : Continuous r) (hs : Continuous s) (hf : Continuous f) :
    Continuous fun x => (star (ω (r x) (s x) : 𝓜(ℂ, A))).snd (f x) := by
  simp_rw [DoubleCentralizer.star_snd]
  exact (ω.continuous_fst_apply hr hs hf.star).star

end JointContinuity

/-! ### Abelian group structure on central cocycles -/

/-- The trivial cocycle, assigning `1` to every pair of group elements. -/
instance : One (CentralCocycle α) where
  one :=
    { toFun _ _ := 1
      commute' _ _ _ := Commute.one_left _
      map_one_left' _ := rfl
      map_one_right' _ := rfl
      mul_cocycle' _ _ _ := by simp
      continuous_fst' _ := continuous_const }

@[simp]
theorem one_apply (s t : G) : (1 : CentralCocycle α) s t = 1 :=
  (rfl)

/-- Pointwise multiplication of normalized continuous central cocycles. -/
instance : Mul (CentralCocycle α) where
  mul ω₁ ω₂ :=
    { toFun s t := ω₁ s t * ω₂ s t
      commute' s t m := (ω₁.commute s t m).mul_left (ω₂.commute s t m)
      map_one_left' s := by simp
      map_one_right' s := by simp
      mul_cocycle' r s t := by
        simp only [Submonoid.coe_mul, map_mul]
        calc α.multiplier r (ω₁ s t : 𝓜(ℂ, A)) * α.multiplier r (ω₂ s t : 𝓜(ℂ, A)) *
              ((ω₁ r (s * t) : 𝓜(ℂ, A)) * (ω₂ r (s * t) : 𝓜(ℂ, A)))
            = α.multiplier r (ω₁ s t : 𝓜(ℂ, A)) *
                (α.multiplier r (ω₂ s t : 𝓜(ℂ, A)) * (ω₁ r (s * t) : 𝓜(ℂ, A))) *
                (ω₂ r (s * t) : 𝓜(ℂ, A)) := by simp only [mul_assoc]
          _ = (α.multiplier r (ω₁ s t : 𝓜(ℂ, A)) * (ω₁ r (s * t) : 𝓜(ℂ, A))) *
                (α.multiplier r (ω₂ s t : 𝓜(ℂ, A)) * (ω₂ r (s * t) : 𝓜(ℂ, A))) := by
              rw [← (ω₁.commute r (s * t) _).eq]
              simp only [mul_assoc]
          _ = ((ω₁ r s : 𝓜(ℂ, A)) * (ω₁ (r * s) t : 𝓜(ℂ, A))) *
                ((ω₂ r s : 𝓜(ℂ, A)) * (ω₂ (r * s) t : 𝓜(ℂ, A))) := by
              rw [ω₁.mul_cocycle, ω₂.mul_cocycle]
          _ = (ω₁ r s : 𝓜(ℂ, A)) * ((ω₁ (r * s) t : 𝓜(ℂ, A)) * (ω₂ r s : 𝓜(ℂ, A))) *
                (ω₂ (r * s) t : 𝓜(ℂ, A)) := by simp only [mul_assoc]
          _ = (ω₁ r s : 𝓜(ℂ, A)) * (ω₂ r s : 𝓜(ℂ, A)) *
                ((ω₁ (r * s) t : 𝓜(ℂ, A)) * (ω₂ (r * s) t : 𝓜(ℂ, A))) := by
              rw [(ω₁.commute (r * s) t _).eq]
              simp only [mul_assoc]
      continuous_fst' a := by
        simpa using ω₁.continuous_fst_apply _root_.continuous_fst _root_.continuous_snd
          (ω₂.continuous_fst a) }

@[simp]
theorem mul_apply (ω₁ ω₂ : CentralCocycle α) (s t : G) :
    (ω₁ * ω₂) s t = ω₁ s t * ω₂ s t :=
  (rfl)

/-- Pointwise inverse (adjoint) of a normalized continuous central cocycle. -/
instance : Inv (CentralCocycle α) where
  inv ω :=
    { toFun s t := star (ω s t)
      commute' s t m := ω.commute_star s t m
      map_one_left' s := by simp
      map_one_right' s := by simp
      mul_cocycle' r s t := by
        simp only [Unitary.coe_star, map_star]
        calc star (α.multiplier r (ω s t : 𝓜(ℂ, A))) * star (ω r (s * t) : 𝓜(ℂ, A))
            = star ((ω r (s * t) : 𝓜(ℂ, A)) * α.multiplier r (ω s t : 𝓜(ℂ, A))) :=
              (star_mul _ _).symm
          _ = star (α.multiplier r (ω s t : 𝓜(ℂ, A)) * (ω r (s * t) : 𝓜(ℂ, A))) := by
              rw [(ω.commute r (s * t) _).eq]
          _ = star ((ω (r * s) t : 𝓜(ℂ, A)) * (ω r s : 𝓜(ℂ, A))) := by
              rw [ω.mul_cocycle, (ω.commute r s _).eq]
          _ = star (ω r s : 𝓜(ℂ, A)) * star (ω (r * s) t : 𝓜(ℂ, A)) := star_mul _ _
      continuous_fst' a := ω.continuous_star_fst a }

@[simp]
theorem inv_apply (ω : CentralCocycle α) (s t : G) : ω⁻¹ s t = (ω s t)⁻¹ :=
  (rfl)

theorem coe_inv_apply (ω : CentralCocycle α) (s t : G) :
    ((ω⁻¹ s t : unitary 𝓜(ℂ, A)) : 𝓜(ℂ, A)) = star (ω s t : 𝓜(ℂ, A)) :=
  (rfl)

instance : CommGroup (CentralCocycle α) where
  mul_assoc _ _ _ := ext fun _ _ => mul_assoc _ _ _
  one_mul _ := ext fun _ _ => one_mul _
  mul_one _ := ext fun _ _ => mul_one _
  inv_mul_cancel _ := ext fun _ _ => inv_mul_cancel _
  mul_comm ω₁ ω₂ := ext_coe fun s t => ω₁.commute s t (ω₂ s t : 𝓜(ℂ, A))

instance : Inhabited (CentralCocycle α) := ⟨1⟩

/-! ### Restriction along group homomorphisms and transport by conjugacy -/

section Functoriality

/-- Transport central cocycles along an equality of C⋆-actions, as a multiplicative equivalence. -/
def cast {α β : CStarAction G A} (h : α = β) : CentralCocycle α ≃* CentralCocycle β where
  toFun := h ▸ _root_.id
  invFun := h.symm ▸ _root_.id
  left_inv ω := by subst h; rfl
  right_inv ω := by subst h; rfl
  map_mul' ω₁ ω₂ := by subst h; rfl

@[simp]
theorem cast_apply {α β : CStarAction G A} (h : α = β) (ω : CentralCocycle α) (s t : G) :
    ω.cast h s t = ω s t := by
  subst h; rfl

@[simp]
theorem cast_rfl (ω : CentralCocycle α) : ω.cast rfl = ω :=
  (rfl)

/-- Pull back central cocycles along a continuous group homomorphism, as a group homomorphism. -/
def comp {H : Type*} [Group H] [TopologicalSpace H] (φ : ContinuousMonoidHom H G) :
    CentralCocycle α →* CentralCocycle (α.comp φ) where
  toFun ω :=
    { toFun s t := ω (φ s) (φ t)
      commute' s t := ω.commute (φ s) (φ t)
      map_one_left' s := by simp
      map_one_right' s := by simp
      mul_cocycle' r s t := by
        have hm : (α.comp φ).multiplier r (ω (φ s) (φ t) : 𝓜(ℂ, A)) =
            α.multiplier (φ r) (ω (φ s) (φ t) : 𝓜(ℂ, A)) :=
          DoubleCentralizer.ext_fst fun a => by simp
        rw [hm]
        simpa only [map_mul] using ω.mul_cocycle (φ r) (φ s) (φ t)
      continuous_fst' a := (ω.continuous_fst a).comp (φ.continuous.prodMap φ.continuous) }
  map_one' := ext fun _ _ => rfl
  map_mul' _ _ := ext fun _ _ => rfl

@[simp]
theorem comp_apply {H : Type*} [Group H] [TopologicalSpace H] (φ : ContinuousMonoidHom H G)
    (ω : CentralCocycle α) (s t : H) :
    ω.comp φ s t = ω (φ s) (φ t) :=
  (rfl)

@[simp]
theorem comp_id (ω : CentralCocycle α) :
    (ω.comp (.id G)).cast α.comp_id = ω :=
  ext fun _ _ => by simp

theorem comp_comp {H K : Type*} [Group H] [TopologicalSpace H] [Group K] [TopologicalSpace K]
    (φ : ContinuousMonoidHom H G) (ψ : ContinuousMonoidHom K H) (ω : CentralCocycle α) :
    ((ω.comp φ).comp ψ).cast (α.comp_comp φ ψ) = ω.comp (φ.comp ψ) :=
  ext fun _ _ => by simp

/-- Transport a central cocycle along `e : A ≃⋆ₐ[ℂ] B`. -/
private def conjugateAux {B : Type*} [NonUnitalCStarAlgebra B] {α : CStarAction G A}
    (e : A ≃⋆ₐ[ℂ] B) (ω : CentralCocycle α) : CentralCocycle (α.conjugate e) where
  toFun s t := ⟨DoubleCentralizer.congr e (ω s t),
    Unitary.map_mem (DoubleCentralizer.congr e) (ω s t).prop⟩
  commute' s t m := by
    rw [Commute, SemiconjBy]
    have hm : DoubleCentralizer.congr e ((DoubleCentralizer.congr e).symm m) = m :=
      (DoubleCentralizer.congr e).apply_symm_apply m
    calc DoubleCentralizer.congr e (ω s t : 𝓜(ℂ, A)) * m
        = DoubleCentralizer.congr e
            ((ω s t : 𝓜(ℂ, A)) * (DoubleCentralizer.congr e).symm m) := by
          rw [map_mul, hm]
      _ = DoubleCentralizer.congr e
            ((DoubleCentralizer.congr e).symm m * (ω s t : 𝓜(ℂ, A))) := by
          rw [(ω.commute s t _).eq]
      _ = m * DoubleCentralizer.congr e (ω s t : 𝓜(ℂ, A)) := by
          rw [map_mul, hm]
  map_one_left' s := Subtype.ext <| by simp
  map_one_right' s := Subtype.ext <| by simp
  mul_cocycle' r s t := by
    have hmult (x : 𝓜(ℂ, A)) :
        (α.conjugate e).multiplier r (DoubleCentralizer.congr e x) =
          DoubleCentralizer.congr e (α.multiplier r x) := by
      simp only [CStarAction.multiplier_apply]
      exact DoubleCentralizer.ext_fst fun b => by simp
    simp only
    rw [hmult, ← map_mul, ω.mul_cocycle, map_mul]
  continuous_fst' b := by
    simp only [DoubleCentralizer.congr_apply_fst]
    exact (StarAlgEquiv.isometry e).continuous.comp (ω.continuous_fst (e.symm b))

private theorem coe_conjugateAux_apply {B : Type*} [NonUnitalCStarAlgebra B]
    (e : A ≃⋆ₐ[ℂ] B) (ω : CentralCocycle α) (s t : G) :
    ((conjugateAux e ω s t : unitary 𝓜(ℂ, B)) : 𝓜(ℂ, B)) =
      DoubleCentralizer.congr e (ω s t : 𝓜(ℂ, A)) :=
  rfl

/-- Transport central cocycles along a star-algebra equivalence `e : A ≃⋆ₐ[ℂ] B`, as a
multiplicative equivalence with `CentralCocycle (α.conjugate e)`. -/
def conjugate {B : Type*} [NonUnitalCStarAlgebra B] (e : A ≃⋆ₐ[ℂ] B) :
    CentralCocycle α ≃* CentralCocycle (α.conjugate e) where
  toFun := conjugateAux e
  invFun ω := (conjugateAux e.symm ω).cast (α.conjugate_symm e)
  left_inv ω := ext_coe fun s t => by
    simp only [cast_apply, coe_conjugateAux_apply, ← DoubleCentralizer.congr_symm,
      StarAlgEquiv.symm_apply_apply]
  right_inv ω := ext_coe fun s t => by
    simp only [coe_conjugateAux_apply, cast_apply, ← DoubleCentralizer.congr_symm,
      StarAlgEquiv.apply_symm_apply]
  map_mul' ω₁ ω₂ := ext_coe fun s t => map_mul (DoubleCentralizer.congr e) _ _

@[simp]
theorem coe_conjugate_apply {B : Type*} [NonUnitalCStarAlgebra B] (e : A ≃⋆ₐ[ℂ] B)
    (ω : CentralCocycle α) (s t : G) :
    ((ω.conjugate e s t : unitary 𝓜(ℂ, B)) : 𝓜(ℂ, B)) =
      DoubleCentralizer.congr e (ω s t : 𝓜(ℂ, A)) :=
  (rfl)

theorem conjugate_apply_fst {B : Type*} [NonUnitalCStarAlgebra B] (e : A ≃⋆ₐ[ℂ] B)
    (ω : CentralCocycle α) (s t : G) (b : B) :
    (ω.conjugate e s t : 𝓜(ℂ, B)).fst b = e ((ω s t : 𝓜(ℂ, A)).fst (e.symm b)) := by
  simp

theorem conjugate_apply_snd {B : Type*} [NonUnitalCStarAlgebra B] (e : A ≃⋆ₐ[ℂ] B)
    (ω : CentralCocycle α) (s t : G) (b : B) :
    (ω.conjugate e s t : 𝓜(ℂ, B)).snd b = e ((ω s t : 𝓜(ℂ, A)).snd (e.symm b)) := by
  simp

@[simp]
theorem conjugate_refl (ω : CentralCocycle α) :
    (ω.conjugate (.refl ℂ A)).cast α.conjugate_refl = ω :=
  ext_coe fun _ _ => by simp

theorem conjugate_conjugate {B C : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
    (e : A ≃⋆ₐ[ℂ] B) (f : B ≃⋆ₐ[ℂ] C) (ω : CentralCocycle α) :
    ((ω.conjugate e).conjugate f).cast (α.conjugate_conjugate e f) =
      ω.conjugate (e.trans f) :=
  ext_coe fun _ _ => by simp [DoubleCentralizer.congr_trans]

@[simp]
theorem conjugate_symm {B : Type*} [NonUnitalCStarAlgebra B] (e : A ≃⋆ₐ[ℂ] B)
    (ω : CentralCocycle α) :
    ((ω.conjugate e).conjugate e.symm).cast (α.conjugate_symm e) = ω :=
  (conjugate e).symm_apply_apply ω

theorem conjugate_comp {H B : Type*} [Group H] [TopologicalSpace H] [NonUnitalCStarAlgebra B]
    (e : A ≃⋆ₐ[ℂ] B) (φ : ContinuousMonoidHom H G) (ω : CentralCocycle α) :
    ((ω.conjugate e).comp φ).cast (α.conjugate_comp e φ) = (ω.comp φ).conjugate e :=
  ext_coe fun _ _ => by simp

end Functoriality

/-! ### Scalar circle-valued cocycles -/

/-- Embed `Circle` into `unitary 𝓜(ℂ, A)` via `z ↦ (z : ℂ) • 1`, as a monoid homomorphism. -/
def circleToUnitary : Circle →* unitary 𝓜(ℂ, A) where
  toFun z := ⟨(z : ℂ) • (1 : 𝓜(ℂ, A)), by
    rw [Unitary.mem_iff]
    have hz1 : star (z : ℂ) * (z : ℂ) = 1 := by
      rw [Complex.star_def, ← Circle.coe_inv_eq_conj, Circle.coe_inv,
        inv_mul_cancel₀ z.coe_ne_zero]
    have hz2 : (z : ℂ) * star (z : ℂ) = 1 := by rw [mul_comm, hz1]
    constructor
    · rw [star_smul, star_one, smul_mul_smul_comm, mul_one, hz1, one_smul]
    · rw [star_smul, star_one, smul_mul_smul_comm, mul_one, hz2, one_smul]⟩
  map_one' := Subtype.ext <| by simp
  map_mul' z w := Subtype.ext <| by
    simp only [Submonoid.coe_mul, Circle.coe_mul, smul_mul_smul_comm, mul_one]

@[simp]
theorem coe_circleToUnitary (z : Circle) :
    (circleToUnitary (A := A) z : 𝓜(ℂ, A)) = (z : ℂ) • 1 :=
  (rfl)

theorem circleToUnitary_fst (z : Circle) (a : A) :
    (circleToUnitary (A := A) z : 𝓜(ℂ, A)).fst a = (z : ℂ) • a :=
  (rfl)

theorem circleToUnitary_snd (z : Circle) (a : A) :
    (circleToUnitary (A := A) z : 𝓜(ℂ, A)).snd a = (z : ℂ) • a :=
  (rfl)

variable (α) in
/-- Every normalized continuous circle-valued 2-cocycle `σ : G → G → Circle` defines a central
multiplier cocycle `(s, t) ↦ (σ s t : ℂ) • 1` on any C⋆-dynamical system `(A, G, α)`. -/
def ofCircle (σ : G → G → Circle) (hcont : Continuous (Function.uncurry σ))
    (h1l : ∀ s, σ 1 s = 1) (h1r : ∀ s, σ s 1 = 1)
    (hcoc : ∀ r s t, σ s t * σ r (s * t) = σ r s * σ (r * s) t) : CentralCocycle α where
  toFun s t := circleToUnitary (σ s t)
  commute' s t m := by simp [Commute, SemiconjBy, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  map_one_left' s := by simp [h1l]
  map_one_right' s := by simp [h1r]
  mul_cocycle' r s t := by
    have h := congrArg (Subtype.val : Circle → ℂ) (hcoc r s t)
    simp only [coe_circleToUnitary, map_smul, map_one, smul_mul_smul_comm, mul_one]
    exact congrArg (· • (1 : 𝓜(ℂ, A))) h
  continuous_fst' a :=
    (continuous_subtype_val.comp hcont).smul continuous_const

@[simp]
theorem ofCircle_apply (σ : G → G → Circle) (hcont h1l h1r hcoc) (s t : G) :
    ofCircle α σ hcont h1l h1r hcoc s t = circleToUnitary (σ s t) :=
  (rfl)

end CentralCocycle

end TauCeti.CStarAction
