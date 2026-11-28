/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.Lang.Basic
public import TauCeti.AlgebraicGeometry.Frobenius.FieldPoints
import TauCeti.AlgebraicGeometry.Morphisms.Epi

/-!
# Frobenius on the fibres of the Lang map

Let `G` be a commutative group scheme over a finite field `k` with `q` elements.
For a finite extension `E/k` of degree `n`, the product of the Frobenius conjugates of
`x ∈ G(E)` descends to a point `N(x) ∈ G(k)`. This is the homomorphism `rationalPointsNorm`.

On a Lang lift `t` with `F(t) / t = x`, the arithmetic Frobenius satisfies
`Fⁿ(t) = t · N(x)` by the telescoping identity `langMap_comp_frobeniusNorm`. Geometric
Frobenius therefore acts on the fibre by `t ↦ t / N(x)`. Pullback of functions on the fibre
uses the inverse action, which accounts for the sign in the character-sheaf trace formula.

## References

* G. Laumon, *Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil*, Publ. Math. IHÉS 65 (1987), Exemple (1.1.3), especially (1.1.3.3).
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace TauCeti.GroupScheme

variable (k : Type u) [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] (a : ℕ)
  (ha : Nat.card k = p ^ a)
variable {G : CommGrp (Over (Spec (.of k)))}

/-- Arithmetic Frobenius on a lift `t` of `x` through the Lang map. Its `n`-th power
translates `t` by the product of the first `n` Frobenius conjugates of `x`. -/
theorem qPowerFrobeniusOver_pow_comp_of_comp_langMap_eq
    {T : Over (Spec (.of k))} {t x : T ⟶ G.X}
    (ht : t ≫ (langMap k a ha G).hom.hom.hom = x) (n : ℕ) :
    (End.of (qPowerFrobeniusOver k a ha T) ^ n).asHom ≫ t =
      t * (x ≫ (frobeniusNorm k a ha G n).hom.hom.hom) := by
  apply div_eq_iff_eq_mul'.mp
  calc
    _ = t ≫ ((End.of (qPowerFrobeniusCommGrpHom k a ha G) ^ n).asHom - 𝟙 G).hom.hom.hom := by
      simp [GrpObj.comp_div, comp_qPowerFrobeniusOver_pow]
    _ = _ := by
      rw [← langMap_comp_frobeniusNorm, ← ht]
      simp

variable (E : Type u) [Field E] [Algebra k E] [Module.Finite k E]

private theorem exists_toUnit_comp_eq_comp_frobeniusNorm
    (x : Over.mk (Spec.algebraMap k E) ⟶ G.X) :
    ∃ y : 𝟙_ (Over (Spec (.of k))) ⟶ G.X, toUnit _ ≫ y =
      x ≫ (frobeniusNorm k a ha G (Module.finrank k E)).hom.hom.hom := by
  apply (exists_toUnit_comp_eq_iff_qPowerFrobeniusOver_comp_eq k a ha E _).2
  apply (exists_comp_langKernelι_iff k a ha _).1
  apply exists_comp_langKernelι_eq_comp_frobeniusNorm
  have : CharP E p := charP_of_injective_algebraMap (algebraMap k E).injective p
  have hF : (End.of (qPowerFrobeniusOver k a ha (Over.mk (Spec.algebraMap k E))) ^
      Module.finrank k E).asHom = 𝟙 _ := by
    apply Over.OverMorphism.ext
    rw [qPowerFrobeniusOver_pow_asHom_left]
    apply iterateFrobenius_spec_eq_id
    rw [Module.natCard_eq_pow_finrank (K := k), ha, pow_mul]
  rw [hF, Category.id_comp]

variable (G) in
/-- The norm homomorphism `G(E) → G(k)` for a finite extension of finite fields.
After extension of scalars to `E`, it is the product of the Frobenius conjugates. -/
noncomputable def rationalPointsNorm :
    (Over.mk (Spec.algebraMap k E) ⟶ G.X) →* (𝟙_ (Over (Spec (.of k))) ⟶ G.X) :=
  MonoidHom.mk' (fun x ↦ (exists_toUnit_comp_eq_comp_frobeniusNorm k a ha E x).choose) <| by
    intro x y
    have : Epi (toUnit (Over.mk (Spec.algebraMap k E))) := Over.epi_of_epi_left _
    apply (cancel_epi (toUnit (Over.mk (Spec.algebraMap k E)))).1
    rw [comp_mul]
    simp_rw [(exists_toUnit_comp_eq_comp_frobeniusNorm k a ha E _).choose_spec]
    exact mul_comp _ _ _

/-- Extending the rational norm to `E` recovers the scheme-theoretic Frobenius norm. -/
@[simp] theorem toUnit_comp_rationalPointsNorm (x : Over.mk (Spec.algebraMap k E) ⟶ G.X) :
    toUnit _ ≫ rationalPointsNorm k a ha G E x =
      x ≫ (frobeniusNorm k a ha G (Module.finrank k E)).hom.hom.hom :=
  (exists_toUnit_comp_eq_comp_frobeniusNorm k a ha E x).choose_spec

/-- Over a point `x ∈ G(E)`, arithmetic Frobenius of degree `[E : k]` translates every
Lang lift by the base-field point `N(x)`, pulled back to the test scheme. -/
theorem qPowerFrobeniusOver_pow_comp_eq_mul_rationalPointsNorm {T : Over (Spec (.of k))}
    (i : T ⟶ Over.mk (Spec.algebraMap k E)) (x : Over.mk (Spec.algebraMap k E) ⟶ G.X)
    (t : T ⟶ G.X) (ht : t ≫ (langMap k a ha G).hom.hom.hom = i ≫ x) :
    (End.of (qPowerFrobeniusOver k a ha T) ^ Module.finrank k E).asHom ≫ t =
      t * (toUnit T ≫ rationalPointsNorm k a ha G E x) := by
  rw [qPowerFrobeniusOver_pow_comp_of_comp_langMap_eq k a ha ht, Category.assoc,
    ← toUnit_comp_rationalPointsNorm, ← Category.assoc, comp_toUnit]

/-- On a Lang fibre over `x ∈ G(E)`, geometric Frobenius sends `t` to `t / N(x)`. Here
`i` specifies the embedding of `E` in the field of values `Ω` of the lift. -/
theorem geometricFrobenius_comp_eq_div_rationalPointsNorm
    [Fintype k] (Ω : Type u) [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    (i : Over.mk (Spec.algebraMap k Ω) ⟶ Over.mk (Spec.algebraMap k E))
    (x : Over.mk (Spec.algebraMap k E) ⟶ G.X)
    (t : Over.mk (Spec.algebraMap k Ω) ⟶ G.X)
    (ht : t ≫ (langMap k a ha G).hom.hom.hom = i ≫ x) :
    Spec.map (CommRingCat.ofHom
      (((FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ Module.finrank k E)⁻¹ : Ω ≃ₐ[k] Ω) :
        Ω →+* Ω)) ≫ t.left = (t / (toUnit _ ≫ rationalPointsNorm k a ha G E x)).left := by
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ Module.finrank k E
  have h : (End.of (qPowerFrobeniusOver k a ha _) ^ Module.finrank k E).asHom ≫
      (t / (toUnit _ ≫ rationalPointsNorm k a ha G E x)) = t := by
    rw [GrpObj.comp_div, qPowerFrobeniusOver_pow_comp_eq_mul_rationalPointsNorm k a ha E i x t ht,
      ← Category.assoc, comp_toUnit, mul_div_cancel_right]
  have h' := congrArg Over.Hom.left h.symm
  rw [Over.comp_left, qPowerFrobeniusOver_pow_left_eq_SpecMap] at h'
  exact (Iso.inv_comp_eq (Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op)).2 h'

end TauCeti.GroupScheme
