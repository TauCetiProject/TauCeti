/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor
public import TauCeti.Algebra.Category.GradedModuleCat.Coproducts
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Corner
public import Mathlib.Algebra.Homology.Bifunctor

/-!
# Tensor composition of zigzag braid bimodules and complexes

The internally graded balanced tensor bifunctor composes the actual enveloping-algebra
modules used in the zigzag braid complexes. Mathlib's cochain totalization supplies the
cohomological signs; internal degrees add without a further sign.

The full tensor product of vertex braid bimodules vanishes at distinct nonadjacent vertices.
This is the degree-`-2` vanishing needed for the commuting equivalence of braid complexes.

## References

* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*.
* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory MulOpposite
open scoped TensorProduct

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

/-- Use the signed path-length grading for bimodule tensor composition. -/
local instance : GradedAlgebra (zigzagAlgebraInternalGrading k G).piece :=
  zigzagAlgebraIntegerGradedAlgebra k G

/-- Balanced tensor composition in the category of the actual graded zigzag bimodules. -/
-- Its category indices and object assignment must compute for totalization and tensor maps.
noncomputable abbrev zigzagBimoduleTensor :
    GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece ⥤
      GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece ⥤
        GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece :=
  GradedModuleCat.bimoduleTensor (zigzagAlgebraInternalGrading k G)
    (zigzagAlgebraInternalGrading k G) (zigzagAlgebraInternalGrading k G)

/-- The cochain tensor product of the existing two-term graded braid complexes. -/
noncomputable abbrev zigzagBraidComplexTensor (i j : V) :
    CochainComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) ℤ :=
  HomologicalComplex.mapBifunctor (zigzagBraidComplex k G i) (zigzagBraidComplex k G j)
    (zigzagBimoduleTensor k G) (ComplexShape.up ℤ)

section Nonadjacent

variable {k G} {i j : V}

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "E" => Z ⊗[k] Zᵐᵒᵖ
local notation "e" => fun v : V ↦ zigzagAlgebraBasis k G (Sum.inl v)
local notation "U" => zigzagGradedBraidBimodule k G
local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "t" => GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U j)

private theorem vertex_smul_braidBimodule_eq_zero
    (hij : i ≠ j) (hadj : ¬ G.Adj i j) (n : U j) :
    (e i ⊗ₜ[k] (1 : Zᵐᵒᵖ)) • n = 0 := by
  have hcut : ∀ z : E, (e i ⊗ₜ[k] (1 : Zᵐᵒᵖ)) * z * (e j ⊗ₜ[k] op (e j)) = 0 := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul,
        zigzagAlgebraBasis_inl_mul_mul_eq_zero_of_ne_of_not_adj k G hij hadj,
        TensorProduct.zero_tmul]
    | add x y hx hy => simp only [mul_add, add_mul, hx, hy, add_zero]
  apply Subtype.ext
  -- The enveloping action on the cyclic ideal is left multiplication.
  change (e i ⊗ₜ[k] (1 : Zᵐᵒᵖ)) * n.val = 0
  have hn := (mem_zigzagBraidBimodule_iff).1 n.property
  calc
    (e i ⊗ₜ[k] (1 : Zᵐᵒᵖ)) * n.val =
        (e i ⊗ₜ[k] (1 : Zᵐᵒᵖ)) * (n.val * (e j ⊗ₜ[k] op (e j))) := by rw [hn]
    _ = 0 := by rw [← mul_assoc]; exact hcut n.val

/-- Every pure tensor of distinct nonadjacent vertex braid bimodules vanishes. -/
theorem zigzagBraidBimodule_tmul_eq_zero_of_ne_of_not_adj
    (hij : i ≠ j) (hadj : ¬ G.Adj i j) (m : U i) (n : U j) : t m n = 0 := by
  let g : U i := ⟨e i ⊗ₜ[k] op (e i), by
    simpa only [one_mul, mul_one] using tmul_mem_zigzagBraidBimodule i (1 : Z) (1 : Z)⟩
  have hg : ((1 : Z) ⊗ₜ[k] op (e i)) • g = g := by
    apply Subtype.ext
    -- Compute the restricted right vertex action on the cyclic generator.
    change ((1 : Z) ⊗ₜ[k] op (e i)) * (e i ⊗ₜ[k] op (e i)) = e i ⊗ₜ[k] op (e i)
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← op_mul,
      (isIdempotentElem_zigzagAlgebraBasis_inl k G i).eq]
  have hgen : ∀ n : U j, t g n = 0 := by
    intro n
    have h := GradedModuleCat.bimoduleTensorTmul_balance Γ Γ Γ (U i) (U j) (e i) g n
    rw [hg, vertex_smul_braidBimodule_eq_zero hij hadj,
      GradedModuleCat.bimoduleTensorTmul_zero_right] at h
    exact h
  have hscalar : ∀ z : E, t (z • g) n = 0 := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      have hfactor : x ⊗ₜ[k] y = (x ⊗ₜ[k] (1 : Zᵐᵒᵖ)) * ((1 : Z) ⊗ₜ[k] y) := by
        simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hfactor, mul_smul]
      have hout : t ((x ⊗ₜ[k] (1 : Zᵐᵒᵖ)) • (((1 : Z) ⊗ₜ[k] y) • g)) n =
          (x ⊗ₜ[k] (1 : Zᵐᵒᵖ)) • t (((1 : Z) ⊗ₜ[k] y) • g) n := by
        simpa only [← Algebra.TensorProduct.one_def, one_smul] using
          (GradedModuleCat.tmul_smul_bimoduleTensorTmul Γ Γ Γ (U i) (U j)
            x 1 (((1 : Z) ⊗ₜ[k] y) • g) n).symm
      rw [hout]
      have hb := GradedModuleCat.bimoduleTensorTmul_balance Γ Γ Γ (U i) (U j)
        (unop y) g n
      rw [op_unop] at hb
      rw [hb, hgen, smul_zero]
    | add x y hx hy =>
      simp only [add_smul, GradedModuleCat.bimoduleTensorTmul_add_left, hx, hy, add_zero]
  have hm : m.val • g = m := by
    apply Subtype.ext
    -- Membership in the cyclic ideal is the right-idempotent fixed-point equation.
    change m.val * (e i ⊗ₜ[k] op (e i)) = m.val
    exact (mem_zigzagBraidBimodule_iff).1 m.property
  simpa only [hm] using hscalar m.val

/-- The full graded tensor product of distinct nonadjacent vertex braid bimodules vanishes. -/
theorem subsingleton_zigzagBimoduleTensor_of_ne_of_not_adj
    (hij : i ≠ j) (hadj : ¬ G.Adj i j) :
    Subsingleton (((zigzagBimoduleTensor k G).obj (U i)).obj (U j)) := by
  have hzero : ∀ z : GradedModuleCat.bimoduleTensorObj Γ Γ Γ (U i) (U j), z = 0 := by
    intro z
    induction z using GradedModuleCat.bimoduleTensor_induction_on Γ Γ Γ (U i) (U j) with
    | ht m n => exact zigzagBraidBimodule_tmul_eq_zero_of_ne_of_not_adj hij hadj m n
    | ha x y hx hy => simpa only [hx, hy] using (add_zero (0 :
        GradedModuleCat.bimoduleTensorObj Γ Γ Γ (U i) (U j)))
  exact ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩

/-- The full vertex-bimodule tensor is a zero object for distinct nonadjacent vertices. -/
theorem isZero_zigzagBimoduleTensor_of_ne_of_not_adj
    (hij : i ≠ j) (hadj : ¬ G.Adj i j) :
    Limits.IsZero (((zigzagBimoduleTensor k G).obj (U i)).obj (U j)) := by
  have := subsingleton_zigzagBimoduleTensor_of_ne_of_not_adj (k := k) (G := G) hij hadj
  apply (Limits.IsZero.iff_id_eq_zero _).2
  apply GradedModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact Subsingleton.elim _ _

/-- The actual nonadjacent braid-complex product is supported in degrees `-1` and `0`. -/
theorem isZero_zigzagBraidComplexTensor_X_of_ne_of_not_adj
    (hij : i ≠ j) (hadj : ¬ G.Adj i j) {d : ℤ} (h₀ : d ≠ -1) (h₁ : d ≠ 0) :
    Limits.IsZero ((zigzagBraidComplexTensor k G i j).X d) := by
  apply (Limits.IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  -- For cochains indexed by integers, totalization sends the pair `(p, q)` to `p + q`.
  change p + q = d at hpq
  have hz : Limits.IsZero (((zigzagBimoduleTensor k G).obj
      ((zigzagBraidComplex k G i).X p)).obj ((zigzagBraidComplex k G j).X q)) := by
    by_cases hp : p = -1
    · subst p
      by_cases hq : q = -1
      · subst q
        exact (isZero_zigzagBimoduleTensor_of_ne_of_not_adj (k := k) hij hadj).of_iso
          (((zigzagBimoduleTensor k G).flip.obj ((zigzagBraidComplex k G j).X (-1))).mapIso
              (zigzagBraidComplexXIso₀ k G i) ≪≫
            ((zigzagBimoduleTensor k G).obj (U i)).mapIso (zigzagBraidComplexXIso₀ k G j))
      · exact ((zigzagBimoduleTensor k G).obj ((zigzagBraidComplex k G i).X (-1))).map_isZero
          (isZero_zigzagBraidComplex_X j hq (by omega))
    · by_cases hp' : p = 0
      · subst p
        exact ((zigzagBimoduleTensor k G).obj ((zigzagBraidComplex k G i).X 0)).map_isZero
          (isZero_zigzagBraidComplex_X j (by omega) (by omega))
      · exact ((zigzagBimoduleTensor k G).flip.obj ((zigzagBraidComplex k G j).X q)).map_isZero
          (isZero_zigzagBraidComplex_X i hp hp')
  exact hz.eq_of_src _ _

end Nonadjacent

end TauCeti
