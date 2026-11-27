/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Coinduced
public import TauCeti.RepresentationTheory.WeilDeligne.Restriction

/-!
# Induction of raw Weil–Deligne parameters

Let `ι : W' →* W` be a homomorphism of groups with degree maps satisfying
`deg (ι w) = f · deg' w`, for instance the inclusion of the Weil group of a finite extension of
local fields, with `f` the residue degree. For a raw Weil–Deligne parameter `(V', r', N')` for
`W'` and `q ^ f` (`TauCeti.WeilDeligneParameter`), this file constructs the **induced**
parameter on Mathlib's coinduced representation `Representation.coind ι r'`, the space of
functions `F : W → V'` with `F (ι g * w) = r'(g) (F w)`, on which `W` acts by right translation.
Its monodromy is `(N F)(w) = q ^ deg w • N' (F w)`, which is again `W'`-equivariant because
`N' r'(g) = (q ^ f) ^ (-deg' g) • r'(g) N'`, is nilpotent, and satisfies the conjugation relation
for `q`. When `ι` is an open map whose image has finite index, the kernel of the action is open:
it contains the open set of `x` with `t x t⁻¹ ∈ ι(ker r')` for `t` in a finite set of coset
representatives (`TauCeti.WeilDeligneParameter.isOpen_ker_coind`). For an image of finite index
the coinduced representation is the induced one; this file works with the function model and
does not compare it with the tensor-product model `W ⊗_{W'} V'` in left-coset notation.

Induction is right adjoint to restriction: morphisms from the restriction of a parameter `D` for
`W` to `D'` correspond to morphisms from `D` to the induced parameter
(`TauCeti.WeilDeligneParameter.restrictIndHomEquiv`, Frobenius reciprocity), by
`φ ↦ (v ↦ (w ↦ φ (r(w) v)))` with inverse evaluation at `1`.

## Main definitions

* `TauCeti.WeilDeligneParameter.indN`: the monodromy `(N F)(w) = q ^ deg w • N' (F w)` on the
  coinduced representation.
* `TauCeti.WeilDeligneParameter.ind`: the induced parameter along an open map `ι` with image of
  finite index.
* `TauCeti.WeilDeligneParameter.restrictIndHomEquiv`: Frobenius reciprocity.

## Main results

* `TauCeti.WeilDeligneParameter.N_r_apply`: `N (r(w) v) = q ^ (-deg w) • r(w) (N v)`.
* `TauCeti.WeilDeligneParameter.isOpen_ker_coind`: the coinduced action has open kernel.
* `TauCeti.WeilDeligneParameter.coind_mul_indN`: the conjugation relation for the induced
  monodromy.

## References

* P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*, in *Modular functions
  of one variable II*, Lecture Notes in Math. 349 (1973), §8.4.1, p. 568.
-/

public section

noncomputable section

namespace TauCeti

namespace WeilDeligneParameter

open _root_.Representation

variable {E W W' V V' : Type*} [Field E] [Group W] [Group W']
  [TopologicalSpace W'] [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
  {deg : W →* Multiplicative ℤ} {deg' : W' →* Multiplicative ℤ} {q : ℕ}

/-- The conjugation relation in the form `N (r(w) v) = q ^ (-deg w) • r(w) (N v)`. -/
theorem N_r_apply [TopologicalSpace W] (D : WeilDeligneParameter E W V deg q) (w : W) (v : V) :
    D.N (D.r w v) = (q : E) ^ (-(deg w).toAdd) • D.r w (D.N v) := by
  have h := D.r_apply_N_apply w⁻¹ (D.r w v)
  rw [inv_self_apply, map_inv deg w, toAdd_inv] at h
  rw [← self_inv_apply D.r w (D.N (D.r w v)), h, map_smul]

variable (ι : W' →* W) (f : ℕ) (hf : ∀ w, (deg (ι w)).toAdd = f * (deg' w).toAdd)
  (hq : (q : E) ≠ 0)

include hf hq in
/-- The monodromy formula preserves `W'`-equivariance. -/
theorem indN_mem (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) {F : W → V'}
    (hF : F ∈ coindV ι D'.r) :
    (fun w ↦ (q : E) ^ (deg w).toAdd • D'.N (F w)) ∈ coindV ι D'.r := by
  intro g w
  beta_reduce
  rw [hF g w, N_r_apply, map_smul, smul_smul, map_mul, toAdd_mul, hf, Nat.cast_pow,
    ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hq]
  congr 2
  ring

/-- The **monodromy of the induced parameter**: `(N F)(w) = q ^ deg w • N' (F w)` on the
coinduced representation. -/
def indN (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) : Module.End E (coindV ι D'.r) where
  toFun F := ⟨fun w ↦ (q : E) ^ (deg w).toAdd • D'.N (F.val w), indN_mem ι f hf hq D' F.property⟩
  map_add' F G := by
    ext w
    simp [smul_add]
  map_smul' a F := by
    ext w
    simp [smul_comm a]

variable {ι f hf hq}

@[simp]
theorem indN_apply (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) (F : coindV ι D'.r)
    (w : W) : (indN ι f hf hq D' F).val w = (q : E) ^ (deg w).toAdd • D'.N (F.val w) :=
  (rfl)

omit [TopologicalSpace W'] in
/-- The coinduced action is right translation. -/
theorem coind_apply_val (ρ : _root_.Representation E W' V') (x : W) (F : coindV ι ρ) (w : W) :
    (coind ι ρ x F).val w = F.val (w * x) :=
  (rfl)

/-- Powers of the induced monodromy: `(N ^ k F)(w) = q ^ (k deg w) • N' ^ k (F w)`. -/
theorem indN_pow_apply (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) (k : ℕ)
    (F : coindV ι D'.r) (w : W) :
    ((indN ι f hf hq D' ^ k) F).val w = ((q : E) ^ (deg w).toAdd) ^ k • (D'.N ^ k) (F.val w) := by
  induction k generalizing F with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, indN_apply, pow_succ, pow_succ,
      mul_apply_eq_comp, map_smul, smul_smul]

/-- The induced monodromy is nilpotent. -/
theorem isNilpotent_indN (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) :
    IsNilpotent (indN ι f hf hq D') := by
  obtain ⟨k, hk⟩ := D'.isNilpotent_N
  refine ⟨k, LinearMap.ext fun F ↦ Subtype.ext (funext fun w ↦ ?_)⟩
  rw [indN_pow_apply, hk]
  simp

/-- The induced monodromy satisfies the conjugation relation for `q`. -/
theorem coind_mul_indN (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) (x : W) :
    coind ι D'.r x * indN ι f hf hq D' * coind ι D'.r x⁻¹ =
      (q : E) ^ (deg x).toAdd • indN ι f hf hq D' := by
  refine LinearMap.ext fun F ↦ Subtype.ext (funext fun w ↦ ?_)
  have h : ((coind ι D'.r x * indN ι f hf hq D' * coind ι D'.r x⁻¹) F).val w =
      (q : E) ^ (deg (w * x)).toAdd • D'.N (F.val (w * x * x⁻¹)) :=
    rfl
  rw [h, mul_inv_cancel_right, map_mul, toAdd_mul, zpow_add₀ hq, LinearMap.smul_apply,
    Submodule.coe_smul, Pi.smul_apply, indN_apply, smul_smul, mul_comm]

section Topology

variable [TopologicalSpace W] [ContinuousMul W]

/-- **The coinduced action has open kernel.** If `ι : W' →* W` is an open map whose image has
finite index and `ρ` has open kernel, the coinduced representation has open kernel: it contains
the open set of `x` with `t x t⁻¹ ∈ ι(ker ρ)` for `t` in a finite set of coset representatives. -/
theorem isOpen_ker_coind (hι : IsOpenMap ι) [ι.range.FiniteIndex]
    (ρ : _root_.Representation E W' V') (hρ : IsOpen (ρ.ker : Set W')) :
    IsOpen ((coind ι ρ).ker : Set W) := by
  have : Finite (W ⧸ ι.range) := Subgroup.finite_quotient_of_finiteIndex
  let t : W ⧸ ι.range → W := fun c ↦ (Quotient.out c)⁻¹
  let S : Set W := ⋂ c, (fun x ↦ t c * x * (t c)⁻¹) ⁻¹' (ι '' (ρ.ker : Set W'))
  have hS : IsOpen S := isOpen_iInter_of_finite fun c ↦ (hι _ hρ).preimage (by fun_prop)
  have h1 : (1 : W) ∈ S := Set.mem_iInter.mpr fun c ↦ ⟨1, ρ.ker.one_mem, by simp⟩
  have hSK : S ⊆ (coind ι ρ).ker := by
    intro x hx
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    refine LinearMap.ext fun F ↦ Subtype.ext (funext fun y ↦ ?_)
    obtain ⟨⟨_, h, rfl⟩, hmk⟩ := QuotientGroup.mk_out_eq_mul ι.range y⁻¹
    set c : W ⧸ ι.range := QuotientGroup.mk y⁻¹
    have hy : y = ι h * t c := by
      simp only [t, c, hmk, mul_inv_rev, inv_inv, mul_inv_cancel_left]
    obtain ⟨k, hk, hkx⟩ := Set.mem_iInter.mp hx c
    have hyx : y * x = ι (h * k) * t c := by
      rw [map_mul, hkx, hy]
      group
    have hk1 : ρ k = 1 := MonoidHom.mem_ker.mp hk
    calc F.val (y * x) = F.val (ι (h * k) * t c) := by rw [hyx]
      _ = ρ (h * k) (F.val (t c)) := F.property _ _
      _ = ρ h (F.val (t c)) := by rw [map_mul, hk1, mul_one]
      _ = F.val y := by rw [← F.property, ← hy]
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hS.mem_nhds h1) hSK)

/-- The **induced parameter** of a raw Weil–Deligne parameter `(V', r', N')` for `W'` and
`q ^ f` along `ι : W' →* W` with `deg (ι w) = f · deg' w`, for `ι` an open map with image of
finite index: the coinduced representation `Representation.coind ι r'` with monodromy
`(N F)(w) = q ^ deg w • N' (F w)`. -/
def ind (ι : W' →* W) (f : ℕ) (hf : ∀ w, (deg (ι w)).toAdd = f * (deg' w).toAdd)
    (hq : (q : E) ≠ 0) (hι : IsOpenMap ι) [ι.range.FiniteIndex]
    (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) :
    WeilDeligneParameter E W (coindV ι D'.r) deg q where
  r := coind ι D'.r
  isOpen_ker := isOpen_ker_coind hι D'.r D'.isOpen_ker
  N := indN ι f hf hq D'
  isNilpotent_N := isNilpotent_indN D'
  conj_N := coind_mul_indN D'

variable {hι : IsOpenMap ι} [ι.range.FiniteIndex]

@[simp]
theorem ind_r (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) :
    (ind ι f hf hq hι D').r = coind ι D'.r :=
  (rfl)

@[simp]
theorem ind_N (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) :
    (ind ι f hf hq hι D').N = indN ι f hf hq D' :=
  (rfl)

variable (hι) (hιc : Continuous ι)

/-- The morphism to the induced parameter corresponding to a morphism from the restriction:
`v ↦ (w ↦ φ (r(w) v))`. -/
def Hom.toInd {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W' V' deg' (q ^ f)}
    (φ : Hom (D.restrict ι hιc f hf) D') : Hom D (ind ι f hf hq hι D') where
  toLinearMap := LinearMap.codRestrict (coindV ι D'.r)
    (LinearMap.pi fun w ↦ φ.toLinearMap ∘ₗ D.r w) fun v g w ↦ by
      simpa [map_mul] using φ.map_r_apply g (D.r w v)
  isIntertwining' x := by
    refine LinearMap.ext fun v ↦ Subtype.ext (funext fun w ↦ ?_)
    change φ (D.r w (D.r x v)) = φ (D.r (w * x) v)
    rw [map_mul, mul_apply_eq_comp]
  comp_N := by
    refine LinearMap.ext fun v ↦ Subtype.ext (funext fun w ↦ ?_)
    change φ (D.r w (D.N v)) = (q : E) ^ (deg w).toAdd • D'.N (φ (D.r w v))
    rw [r_apply_N_apply, map_smul]
    exact congrArg _ (by simpa using φ.map_N_apply (D.r w v))

@[simp]
theorem Hom.toInd_apply_val {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W' V' deg' (q ^ f)} (φ : Hom (D.restrict ι hιc f hf) D') (v : V)
    (w : W) : ((φ.toInd hι hιc : Hom D (ind ι f hf hq hι D')) v).val w = φ (D.r w v) :=
  (rfl)

/-- The morphism from the restriction corresponding to a morphism to the induced parameter:
evaluation at `1`. -/
def Hom.ofInd {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W' V' deg' (q ^ f)}
    (Ψ : Hom D (ind ι f hf hq hι D')) : Hom (D.restrict ι hιc f hf) D' where
  toLinearMap := (LinearMap.proj 1 ∘ₗ (coindV ι D'.r).subtype) ∘ₗ Ψ.toLinearMap
  isIntertwining' g := by
    refine LinearMap.ext fun v ↦ ?_
    simp only [LinearMap.comp_apply, restrict_r_apply]
    change (Ψ (D.r (ι g) v)).val 1 = D'.r g ((Ψ v).val 1)
    rw [Ψ.map_r_apply, ind_r, coind_apply_val, one_mul]
    simpa using (Ψ v).property g 1
  comp_N := by
    refine LinearMap.ext fun v ↦ ?_
    have h := congrArg (fun F : coindV ι D'.r ↦ F.val 1) (Ψ.map_N_apply v)
    simpa using h

/-- **Frobenius reciprocity for Weil–Deligne parameters**: morphisms from the restriction of `D`
to `D'` correspond to morphisms from `D` to the induced parameter of `D'`. -/
def restrictIndHomEquiv (D : WeilDeligneParameter E W V deg q)
    (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) :
    Hom (D.restrict ι hιc f hf) D' ≃ Hom D (ind ι f hf hq hι D') where
  toFun φ := φ.toInd hι hιc
  invFun Ψ := Ψ.ofInd hι hιc
  left_inv φ := by
    ext v
    change φ (D.r 1 v) = φ v
    rw [map_one, one_apply_eq_self]
  right_inv Ψ := by
    ext v w
    change (Ψ (D.r w v)).val 1 = (Ψ v).val w
    rw [Ψ.map_r_apply, ind_r, coind_apply_val, one_mul]

end Topology

end WeilDeligneParameter

end TauCeti
