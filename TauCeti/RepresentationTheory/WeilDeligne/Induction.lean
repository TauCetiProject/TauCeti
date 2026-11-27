/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Coinduced
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
`N' r'(g) = (q ^ f) ^ (-deg' g) • r'(g) N'` (`TauCeti.WeilDeligneParameter.N_apply_r_apply`), is
nilpotent, and satisfies the conjugation relation for `q`. When `ι` is an open map whose image has
finite index, the kernel of the action is open (`Representation.isOpen_ker_coind`). For an image of
finite index the coinduced representation is the induced one; this file works with the function
model and does not compare it with the tensor-product model `W ⊗_{W'} V'` in left-coset notation.

Induction is right adjoint to restriction: morphisms from the restriction of a parameter `D` for
`W` to `D'` correspond to morphisms from `D` to the induced parameter
(`TauCeti.WeilDeligneParameter.restrictIndHomEquiv`, Frobenius reciprocity), by
`φ ↦ (v ↦ (w ↦ φ (r(w) v)))` with inverse evaluation at `1`. These maps adapt Mathlib's
`Rep.resCoindToHom` and `Rep.resCoindHomEquiv` (the hom-equivalence of `Rep.resCoindAdjunction`)
to parameters with monodromy. Induction is functorial (`TauCeti.WeilDeligneParameter.Hom.indMap`,
`F ↦ φ ∘ F`), and Frobenius reciprocity is natural in both parameters
(`TauCeti.WeilDeligneParameter.Hom.toInd_comp`,
`TauCeti.WeilDeligneParameter.Hom.toInd_comp_restrict`).

## Main definitions

* `TauCeti.WeilDeligneParameter.indN`: the monodromy `(N F)(w) = q ^ deg w • N' (F w)` on the
  coinduced representation.
* `TauCeti.WeilDeligneParameter.ind`: the induced parameter along an open map `ι` with image of
  finite index.
* `TauCeti.WeilDeligneParameter.restrictIndHomEquiv`: Frobenius reciprocity.
* `TauCeti.WeilDeligneParameter.Hom.indMap`: the induction of a morphism of parameters.

## Main results

* `TauCeti.WeilDeligneParameter.coind_mul_indN_mul_coind_inv`: the conjugation relation for the
  induced monodromy.

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

variable (ι : W' →* W) (f : ℕ) (hf : ∀ w, (deg (ι w)).toAdd = f * (deg' w).toAdd)
  (hq : (q : E) ≠ 0)

include hf hq in
/-- The monodromy formula preserves `W'`-equivariance. -/
theorem indN_mem (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) {F : W → V'}
    (hF : F ∈ coindV ι D'.r) :
    (fun w ↦ (q : E) ^ (deg w).toAdd • D'.N (F w)) ∈ coindV ι D'.r := by
  intro g w
  -- The exponent identity `deg (ι g * w) - f deg' g = deg w`.
  have hexp : (q : E) ^ (deg (ι g * w)).toAdd * ((q ^ f : ℕ) : E) ^ (-(deg' g).toAdd) =
      (q : E) ^ (deg w).toAdd := by
    rw [Nat.cast_pow, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hq, map_mul, toAdd_mul, hf]
    ring_nf
  simp only [hF g w, N_apply_r_apply, map_smul, smul_smul, hexp]

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

/-- Powers of the induced monodromy: `(N ^ k F)(w) = q ^ (k deg w) • N' ^ k (F w)`. -/
theorem indN_pow_apply (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) (k : ℕ)
    (F : coindV ι D'.r) (w : W) :
    ((indN ι f hf hq D' ^ k) F).val w = ((q : E) ^ (deg w).toAdd) ^ k • (D'.N ^ k) (F.val w) := by
  induction k generalizing F with
  | zero => simp
  | succ k ih =>
    simp [pow_succ, mul_apply_eq_comp, ih, smul_smul]

/-- The induced monodromy is nilpotent. -/
theorem isNilpotent_indN (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) :
    IsNilpotent (indN ι f hf hq D') := by
  obtain ⟨k, hk⟩ := D'.isNilpotent_N
  refine ⟨k, LinearMap.ext fun F ↦ Subtype.ext (funext fun w ↦ ?_)⟩
  rw [indN_pow_apply, hk]
  simp

/-- The induced monodromy satisfies the conjugation relation for `q`. -/
theorem coind_mul_indN_mul_coind_inv (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) (x : W) :
    coind ι D'.r x * indN ι f hf hq D' * coind ι D'.r x⁻¹ =
      (q : E) ^ (deg x).toAdd • indN ι f hf hq D' := by
  refine LinearMap.ext fun F ↦ Subtype.ext (funext fun w ↦ ?_)
  -- The exponent identity `deg (w * x) = deg w + deg x`.
  have hexp :
      (q : E) ^ (deg (w * x)).toAdd = (q : E) ^ (deg x).toAdd * (q : E) ^ (deg w).toAdd := by
    rw [map_mul, toAdd_mul, zpow_add₀ hq, mul_comm]
  simp only [mul_apply_eq_comp, coind_apply_coe_apply, indN_apply, mul_inv_cancel_right, hexp]
  simp [smul_smul]

section Topology

variable [TopologicalSpace W] [SeparatelyContinuousMul W]

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
  conj_N := coind_mul_indN_mul_coind_inv D'

variable {hι : IsOpenMap ι} [ι.range.FiniteIndex]

@[simp]
theorem ind_r (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) :
    (ind ι f hf hq hι D').r = coind ι D'.r :=
  (rfl)

@[simp]
theorem ind_N (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) :
    (ind ι f hf hq hι D').N = indN ι f hf hq D' :=
  (rfl)

/-- A morphism into the induced parameter is determined by its values at `1`:
`(Ψ (r(w) v))(1) = (Ψ v)(w)`. -/
@[simp]
theorem Hom.map_r_apply_val_one {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W' V' deg' (q ^ f)} (Ψ : Hom D (ind ι f hf hq hι D')) (w : W)
    (v : V) : (Ψ (D.r w v)).val 1 = (Ψ v).val w := by
  rw [Ψ.map_r_apply, ind_r, coind_apply_coe_apply, one_mul]

variable (hι) (hιc : Continuous ι)

/-- The morphism to the induced parameter corresponding to a morphism from the restriction:
`v ↦ (w ↦ φ (r(w) v))`. -/
def Hom.toInd {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W' V' deg' (q ^ f)}
    (φ : Hom (D.restrict ι hιc f hf) D') : Hom D (ind ι f hf hq hι D') where
  toLinearMap :=
    { toFun v := ⟨fun w ↦ φ (D.r w v), fun g w ↦ by
        simpa [map_mul] using φ.map_r_apply g (D.r w v)⟩
      map_add' v v' := by ext; simp
      map_smul' a v := by ext; simp }
  isIntertwining' x := by
    refine LinearMap.ext fun v ↦ Subtype.ext (funext fun w ↦ ?_)
    simp only [LinearMap.comp_apply, ind_r, coind_apply_coe_apply]
    simp [map_mul]
  comp_N := by
    refine LinearMap.ext fun v ↦ Subtype.ext (funext fun w ↦ ?_)
    have h := φ.map_N_apply (D.r w v)
    rw [restrict_N] at h
    simp [r_apply_N_apply, h]

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
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply,
      restrict_r_apply, IntertwiningMap.toLinearMap_apply, Hom.coe_toIntertwiningMap]
    rw [Ψ.map_r_apply_val_one]
    simpa using (Ψ v).property g 1
  comp_N := by
    refine LinearMap.ext fun v ↦ ?_
    have h := congrArg (fun F : coindV ι D'.r ↦ F.val 1) (Ψ.map_N_apply v)
    simpa using h

@[simp]
theorem Hom.ofInd_apply {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W' V' deg' (q ^ f)} (Ψ : Hom D (ind ι f hf hq hι D')) (v : V) :
    Ψ.ofInd hι hιc v = (Ψ v).val 1 :=
  (rfl)

/-- **Frobenius reciprocity for Weil–Deligne parameters**: morphisms from the restriction of `D`
to `D'` correspond to morphisms from `D` to the induced parameter of `D'`. -/
def restrictIndHomEquiv (D : WeilDeligneParameter E W V deg q)
    (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) :
    Hom (D.restrict ι hιc f hf) D' ≃ Hom D (ind ι f hf hq hι D') where
  toFun φ := φ.toInd hι hιc
  invFun Ψ := Ψ.ofInd hι hιc
  left_inv φ := by
    ext v
    simp
  right_inv Ψ := by
    ext v w
    simp only [IntertwiningMap.toLinearMap_apply, Hom.coe_toIntertwiningMap]
    rw [Hom.toInd_apply_val, Hom.ofInd_apply, Ψ.map_r_apply_val_one]

@[simp]
theorem restrictIndHomEquiv_apply (D : WeilDeligneParameter E W V deg q)
    (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) (φ : Hom (D.restrict ι hιc f hf) D') :
    restrictIndHomEquiv hι hιc D D' φ = (φ.toInd hι hιc : Hom D (ind ι f hf hq hι D')) :=
  (rfl)

@[simp]
theorem restrictIndHomEquiv_symm_apply (D : WeilDeligneParameter E W V deg q)
    (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) (Ψ : Hom D (ind ι f hf hq hι D')) :
    (restrictIndHomEquiv hι hιc D D').symm Ψ = Ψ.ofInd hι hιc :=
  (rfl)

section Functoriality

variable {V'' : Type*} [AddCommGroup V''] [Module E V'']

/-- **Functoriality of induction**: a morphism `φ : D₁' → D₂'` of parameters for `W'` induces the
morphism `F ↦ φ ∘ F` between the induced parameters. -/
def Hom.indMap {D₁' : WeilDeligneParameter E W' V' deg' (q ^ f)}
    {D₂' : WeilDeligneParameter E W' V'' deg' (q ^ f)} (φ : Hom D₁' D₂') :
    Hom (ind ι f hf hq hι D₁') (ind ι f hf hq hι D₂') where
  toLinearMap :=
    { toFun F := ⟨fun w ↦ φ (F.val w), fun g w ↦ by
      beta_reduce
      rw [F.property g w, φ.map_r_apply]⟩
      map_add' F G := by
        ext
        simp
      map_smul' a F := by
        ext
        simp }
  isIntertwining' x := by
    refine LinearMap.ext fun F ↦ Subtype.ext (funext fun w ↦ ?_)
    simp only [LinearMap.comp_apply, ind_r, coind_apply_coe_apply]
    rfl
  comp_N := by
    refine LinearMap.ext fun F ↦ Subtype.ext (funext fun w ↦ ?_)
    simp [φ.map_N_apply]

@[simp]
theorem Hom.indMap_apply_val {D₁' : WeilDeligneParameter E W' V' deg' (q ^ f)}
    {D₂' : WeilDeligneParameter E W' V'' deg' (q ^ f)} (φ : Hom D₁' D₂')
    (F : coindV ι D₁'.r) (w : W) :
    ((φ.indMap hι : Hom (ind ι f hf hq hι D₁') (ind ι f hf hq hι D₂')) F).val w =
      φ (F.val w) :=
  (rfl)

/-- Induction preserves identities. -/
@[simp]
theorem Hom.indMap_id (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) :
    (Hom.id D').indMap hι = Hom.id (ind ι f hf hq hι D') := by
  ext F w
  simp

/-- Induction preserves composition. -/
@[simp]
theorem Hom.indMap_comp {V''' : Type*} [AddCommGroup V'''] [Module E V''']
    {D₁' : WeilDeligneParameter E W' V' deg' (q ^ f)}
    {D₂' : WeilDeligneParameter E W' V'' deg' (q ^ f)}
    {D₃' : WeilDeligneParameter E W' V''' deg' (q ^ f)} (ψ : Hom D₂' D₃') (φ : Hom D₁' D₂') :
    ((ψ.comp φ).indMap hι : Hom (ind ι f hf hq hι D₁') _) =
      (ψ.indMap hι).comp (φ.indMap hι) := by
  ext F w
  simp

/-- Frobenius reciprocity is natural in the parameter for `W'`: composing with `ψ : D₁' → D₂'`
corresponds to composing with its induction. -/
theorem Hom.toInd_comp {D : WeilDeligneParameter E W V deg q}
    {D₁' : WeilDeligneParameter E W' V' deg' (q ^ f)}
    {D₂' : WeilDeligneParameter E W' V'' deg' (q ^ f)} (ψ : Hom D₁' D₂')
    (φ : Hom (D.restrict ι hιc f hf) D₁') :
    ((ψ.comp φ).toInd hι hιc : Hom D (ind ι f hf hq hι D₂')) =
      (ψ.indMap hι).comp (φ.toInd hι hιc) := by
  ext v w
  simp

/-- Frobenius reciprocity is natural in the parameter for `W`: precomposing with the restriction
of `g : D₀ → D` corresponds to precomposing with `g`. -/
theorem Hom.toInd_comp_restrict {V₀ : Type*} [AddCommGroup V₀] [Module E V₀]
    {D₀ : WeilDeligneParameter E W V₀ deg q} {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W' V' deg' (q ^ f)} (φ : Hom (D.restrict ι hιc f hf) D')
    (g : Hom D₀ D) :
    ((φ.comp g.restrict).toInd hι hιc : Hom D₀ (ind ι f hf hq hι D')) =
      (φ.toInd hι hιc).comp g := by
  ext v w
  simp [g.map_r_apply]

end Functoriality

end Topology

end WeilDeligneParameter

end TauCeti
