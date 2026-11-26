/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.WeilDeligne.Determinant

/-!
# Restriction of raw Weil–Deligne parameters

For a raw Weil–Deligne parameter `(V, r, N)` (`TauCeti.WeilDeligneParameter`) for `W`, `deg` and
`q`, and a continuous homomorphism `ι : W' →* W` of groups with degree maps satisfying
`deg (ι w) = f · deg' w`, this file constructs the **restriction** `(V, r ∘ ι, N)`
(`TauCeti.WeilDeligneParameter.restrict`). It is a raw parameter for `W'` with `q ^ f` in place
of `q`: for the Weil group `W_L ≤ W_F` of a finite extension of local fields, `f` is the residue
degree and `q ^ f` the residue cardinality of `L`.

Restriction is functorial, and commutes with rank-one parameters, direct sums, duals, twists,
tensor products, determinant characters and determinants. The restriction of `Sp(n)` is `Sp(n)`
for `q ^ f`.

## Main definitions

* `TauCeti.WeilDeligneParameter.restrict`: restriction along `ι : W' →* W`.
* `TauCeti.WeilDeligneParameter.Hom.restrict`, `TauCeti.WeilDeligneParameter.Iso.restrict`: the
  restriction of morphisms and isomorphisms.

## Main results

* `TauCeti.WeilDeligneParameter.restrict_det`: restriction commutes with determinants.
* `TauCeti.WeilDeligneParameter.ker_le_comap_ker_of_deg`: `ι` maps `ker deg'` into `ker deg` when
  `deg ∘ ι = f · deg'`.
* `TauCeti.WeilDeligneParameter.restrict_special`: restriction of `Sp(n)`.

## References

* P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*, in *Modular functions
  of one variable II*, Lecture Notes in Math. 349 (1973), §8.4.1, p. 568.
-/

public section

noncomputable section

namespace TauCeti

namespace WeilDeligneParameter

variable {E W W' V V' : Type*} [Field E] [Group W] [TopologicalSpace W] [Group W']
  [TopologicalSpace W'] [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
  {deg : W →* Multiplicative ℤ} {deg' : W' →* Multiplicative ℤ} {q : ℕ}

/-- Composing a homomorphism with open kernel with a continuous homomorphism `ι : W' →* W`
gives a homomorphism with open kernel, since its kernel is the preimage under `ι`. -/
theorem isOpen_ker_comp {G : Type*} [MulOneClass G] {χ : W →* G} (hχ : IsOpen (χ.ker : Set W))
    {ι : W' →* W} (hι : Continuous ι) : IsOpen ((χ.comp ι).ker : Set W') := by
  rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
  exact hχ.preimage hι

variable (ι : W' →* W) (hι : Continuous ι) (f : ℕ)
  (hf : ∀ w, (deg (ι w)).toAdd = f * (deg' w).toAdd)

/-- The **restriction** of a raw Weil–Deligne parameter along a continuous homomorphism
`ι : W' →* W` with `deg (ι w) = f · deg' w`: the parameter `(V, r ∘ ι, N)` for `W'`, with `q ^ f`
in place of `q`. For the Weil group of a finite extension of local fields, `f` is the residue
degree. -/
def restrict (D : WeilDeligneParameter E W V deg q) : WeilDeligneParameter E W' V deg' (q ^ f) where
  r := D.r.comp ι
  isOpen_ker := isOpen_ker_comp D.isOpen_ker hι
  N := D.N
  isNilpotent_N := D.isNilpotent_N
  conj_N w := by simp [D.conj_N, hf, ← zpow_natCast, ← zpow_mul]

variable {ι hι f hf}

@[simp]
theorem restrict_r_apply (D : WeilDeligneParameter E W V deg q) (w : W') :
    (D.restrict ι hι f hf).r w = D.r (ι w) :=
  (rfl)

@[simp]
theorem restrict_N (D : WeilDeligneParameter E W V deg q) : (D.restrict ι hι f hf).N = D.N :=
  (rfl)

omit [TopologicalSpace W] [TopologicalSpace W'] in
/-- A homomorphism `ι : W' →* W` with `deg (ι w) = f · deg' w` maps the kernel of `deg'` into the
kernel of `deg`. -/
theorem ker_le_comap_ker_of_deg (hf : ∀ w, (deg (ι w)).toAdd = f * (deg' w).toAdd) :
    deg'.ker ≤ deg.ker.comap ι :=
  MonoidHom.ker_le_comap_ker_of_comp_eq (f₁ := powMonoidHom f) <| by
    ext w
    simp [hf]

variable {D₁ D₂ D₃ : WeilDeligneParameter E W V deg q}

/-- The restriction of a morphism of parameters. -/
def Hom.restrict {D : WeilDeligneParameter E W V deg q} {D' : WeilDeligneParameter E W V' deg q}
    (g : Hom D D') : Hom (D.restrict ι hι f hf) (D'.restrict ι hι f hf) where
  toLinearMap := g.toLinearMap
  isIntertwining' w := g.comp_r (ι w)
  comp_N := g.comp_N

@[simp]
theorem Hom.restrict_toLinearMap {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W V' deg q} (g : Hom D D') :
    (g.restrict (ι := ι) (hι := hι) (f := f) (hf := hf)).toLinearMap = g.toLinearMap :=
  (rfl)

@[simp]
theorem Hom.restrict_apply {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W V' deg q} (g : Hom D D') (v : V) :
    g.restrict (ι := ι) (hι := hι) (f := f) (hf := hf) v = g v :=
  (rfl)

@[simp]
theorem Hom.restrict_id :
    (Hom.id D₁).restrict (ι := ι) (hι := hι) (f := f) (hf := hf) = Hom.id _ := by
  ext1
  simp

@[simp]
theorem Hom.restrict_comp (g : Hom D₂ D₃) (g' : Hom D₁ D₂) :
    (g.comp g').restrict (ι := ι) (hι := hι) (f := f) (hf := hf) =
      g.restrict.comp g'.restrict := by
  ext1
  simp

/-- The restriction of an isomorphism of parameters. -/
def Iso.restrict {D : WeilDeligneParameter E W V deg q} {D' : WeilDeligneParameter E W V' deg q}
    (g : Iso D D') : Iso (D.restrict ι hι f hf) (D'.restrict ι hι f hf) where
  toLinearEquiv := g.toLinearEquiv
  isIntertwining' w := g.comp_r (ι w)
  comp_N := g.comp_N

@[simp]
theorem Iso.restrict_apply {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W V' deg q} (g : Iso D D') (v : V) :
    g.restrict (ι := ι) (hι := hι) (f := f) (hf := hf) v = g v :=
  (rfl)

@[simp]
theorem Iso.toHom_restrict {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W V' deg q} (g : Iso D D') :
    (g.restrict (ι := ι) (hι := hι) (f := f) (hf := hf)).toHom = g.toHom.restrict :=
  Hom.ext (LinearMap.ext fun v ↦ by simp)

@[simp]
theorem Iso.restrict_refl :
    (Iso.refl D₁).restrict (ι := ι) (hι := hι) (f := f) (hf := hf) = Iso.refl _ :=
  Iso.ext (LinearEquiv.ext fun v ↦ by simp)

@[simp]
theorem Iso.restrict_trans (g : Iso D₁ D₂) (g' : Iso D₂ D₃) :
    (g.trans g').restrict (ι := ι) (hι := hι) (f := f) (hf := hf) =
      g.restrict.trans g'.restrict :=
  Iso.ext (LinearEquiv.ext fun v ↦ by simp)

@[simp]
theorem Iso.restrict_symm (g : Iso D₁ D₂) :
    (g.restrict (ι := ι) (hι := hι) (f := f) (hf := hf)).symm = g.symm.restrict :=
  Iso.ext (LinearEquiv.ext fun v ↦
    g.restrict.injective ((g.restrict.apply_symm_apply v).trans (by simp)))

/-- The restriction of the rank-one parameter of `χ` is the rank-one parameter of `χ ∘ ι`. -/
@[simp]
theorem restrict_ofCharacter (χ : W →* Eˣ) (hχ : IsOpen (χ.ker : Set W)) :
    (ofCharacter deg q χ hχ).restrict ι hι f hf =
      ofCharacter deg' (q ^ f) (χ.comp ι) (isOpen_ker_comp hχ hι) := by
  ext w <;> simp

/-- Restriction commutes with direct sums. -/
@[simp]
theorem restrict_prod (D : WeilDeligneParameter E W V deg q)
    (D' : WeilDeligneParameter E W V' deg q) :
    (D.prod D').restrict ι hι f hf = (D.restrict ι hι f hf).prod (D'.restrict ι hι f hf) := by
  ext w x <;> simp

/-- Restriction commutes with duals. -/
@[simp]
theorem restrict_dual (D : WeilDeligneParameter E W V deg q) :
    D.dual.restrict ι hι f hf = (D.restrict ι hι f hf).dual := by
  ext w φ <;> simp [Representation.dual_apply]

/-- Restriction commutes with determinant characters. -/
@[simp]
theorem detChar_restrict (D : WeilDeligneParameter E W V deg q) :
    (D.restrict ι hι f hf).detChar = D.detChar.comp ι := by
  ext w
  simp

/-- Restriction of `Sp(n)` along `ι` is `Sp(n)` for `W'` and `q ^ f`. -/
@[simp]
theorem restrict_special (hdeg : Continuous deg) (hq : (q : E) ≠ 0) (hdeg' : Continuous deg')
    (hq' : ((q ^ f : ℕ) : E) ≠ 0) (n : ℕ) :
    (special q n hdeg hq).restrict ι hι f hf = special (q ^ f) n hdeg' hq' := by
  ext w v i
  · simp [hf, Nat.cast_pow, ← zpow_natCast, ← zpow_mul, mul_assoc]
  · simp

variable [SeparatelyContinuousMul W] [SeparatelyContinuousMul W']

/-- Restriction commutes with twists: the twist by `χ` restricts to the twist by `χ ∘ ι`. -/
@[simp]
theorem restrict_twist (D : WeilDeligneParameter E W V deg q) (χ : W →* Eˣ)
    (hχ : IsOpen (χ.ker : Set W)) :
    (D.twist χ hχ).restrict ι hι f hf =
      (D.restrict ι hι f hf).twist (χ.comp ι) (isOpen_ker_comp hχ hι) := by
  ext w x <;> simp [Representation.charTwist_apply]

/-- Restriction commutes with tensor products. -/
@[simp]
theorem restrict_tensor (D : WeilDeligneParameter E W V deg q)
    (D' : WeilDeligneParameter E W V' deg q) :
    (D.tensor D').restrict ι hι f hf = (D.restrict ι hι f hf).tensor (D'.restrict ι hι f hf) := by
  ext w x <;> simp

/-- Restriction commutes with determinants. -/
@[simp]
theorem restrict_det (D : WeilDeligneParameter E W V deg q) :
    D.det.restrict ι hι f hf = (D.restrict ι hι f hf).det := by
  ext w <;> simp

end WeilDeligneParameter

end TauCeti
