/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Injective
public import TauCeti.CategoryTheory.Exact.Resolution.Complete.Basic

/-!
# The horseshoe lemma for complete resolutions

Let `X₁ ↪ X₂ ↠ X₃` be a conflation and let `r₁` and `r₃` be complete resolutions of `X₁` and
`X₃`. Then `X₂` has a complete resolution `r₂` with maps of spliced complexes
`r₁ ⟶ r₂ ⟶ r₃` which split in every degree and restrict to the given conflation on the cycles in
degree zero.

The construction proceeds one degree at a time in both directions. In nonnegative degrees it
applies the injective horseshoe lemma
`TauCeti.ExactStructure.exists_conflation_of_conflation_of_injective`, in negative degrees the
projective one `TauCeti.ExactStructure.exists_conflation_biprod_of_conflation_of_projective`.
Each step produces a conflation of cycles `Z₁ⁿ ↪ Z₂ⁿ ↠ Z₃ⁿ` in the next degree and the conflation
`Z₂ⁿ ↪ X₂ⁿ ↠ Z₂ⁿ⁺¹` linking two consecutive degrees, whose middle term splits as an extension of
`X₃ⁿ` by `X₁ⁿ`.

## Main definitions

* `TauCeti.ExactStructure.CompleteResolution.Horseshoe`: a horseshoe of complete resolutions over
  a conflation.
* `TauCeti.ExactStructure.CompleteResolution.horseshoe`: its existence.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Section 4.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Lemma 2.2.8.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable {E : ExactStructure C}

namespace CompleteResolution

variable (r₁ r₃ : E.CompleteResolution)

/-- A conflation `Z₁ⁿ ↪ Z₂ⁿ ↠ Z₃ⁿ` of cycles of two complete resolutions in degree `n`. -/
private structure Row (n : ℤ) where
  Z : C
  v : r₁.Z n ⟶ Z
  w : Z ⟶ r₃.Z n
  zero : v ≫ w = 0
  conflation : E.Conflation (ShortComplex.mk v w zero)

/-- The step from a row in degree `n` to a row in degree `n + 1`: a conflation
`Z₂ⁿ ↪ M ↠ Z₂ⁿ⁺¹` whose middle term splits as an extension of `X₃ⁿ` by `X₁ⁿ`, compatibly with
the conflations of the complete resolutions. -/
private structure Block (n : ℤ) (R : Row r₁ r₃ n) (R' : Row r₁ r₃ (n + 1)) where
  M : C
  left : r₁.X n ⟶ M
  right : M ⟶ r₃.X n
  left_right : left ≫ right = 0
  split : Nonempty (ShortComplex.mk left right left_right).Splitting
  b : R.Z ⟶ M
  c : M ⟶ R'.Z
  b_c : b ≫ c = 0
  conflation : E.Conflation (ShortComplex.mk b c b_c)
  v_b : R.v ≫ b = r₁.ι n ≫ left
  b_right : b ≫ right = R.w ≫ r₃.ι n
  left_c : left ≫ c = r₁.π n ≫ R'.v
  c_w : c ≫ R'.w = right ≫ r₃.π n

variable {r₁ r₃}

/-- A row in degree `n` extends to the next degree, by the injective horseshoe lemma. -/
private theorem nonempty_forward {n : ℤ} (R : Row r₁ r₃ n) :
    Nonempty (Σ R' : Row r₁ r₃ (n + 1), Block r₁ r₃ n R R') := by
  obtain ⟨M, j, q, hjq, ⟨sp⟩, K, b, c, hbc, v, w, hvw, hb, hv, hvb, hbq, hjc, hcw⟩ :=
    E.exists_conflation_of_conflation_of_injective R.conflation (r₁.conflation n)
      (r₃.conflation n) (r₁.isInjective_X n)
  exact ⟨⟨⟨K, v, w, hvw, hv⟩, ⟨M, j, q, hjq, ⟨sp⟩, b, c, hbc, hb, hvb, hbq, hjc, hcw⟩⟩⟩

/-- A row in degree `n + 1` extends to the previous degree, by the projective horseshoe lemma. -/
private theorem nonempty_backward {n : ℤ} (R' : Row r₁ r₃ (n + 1)) :
    Nonempty (Σ R : Row r₁ r₃ n, Block r₁ r₃ n R R') := by
  obtain ⟨K, u, a, hua, v, w, hvw, hu, hv, ha₁, ha₃, hu₁, hu₃⟩ :=
    E.exists_conflation_biprod_of_conflation_of_projective R'.conflation (r₁.conflation n)
      (r₃.conflation n) (r₃.isProjective_X n)
  exact ⟨⟨⟨K, v, w, hvw, hv⟩, ⟨_, biprod.inl, biprod.snd, by simp,
    ⟨ShortComplex.Splitting.ofHasBinaryBiproduct _ _⟩, u, a, hua, hu, hu₁, hu₃, ha₁, ha₃⟩⟩⟩

variable (r₁ r₃) {X₂ : C} (f : r₁.Z 0 ⟶ X₂) (g : X₂ ⟶ r₃.Z 0) (hfg : f ≫ g = 0)
  (hS : E.Conflation (ShortComplex.mk f g hfg))

/-- The rows in nonnegative degrees, starting from the given conflation. -/
@[reducible] private noncomputable def posRow : (k : ℕ) → Row r₁ r₃ k
  | 0 => ⟨X₂, f, g, hfg, hS⟩
  | k + 1 => (nonempty_forward (posRow k)).some.1

/-- The rows in degrees `-k`, for `k : ℕ`, as rows indexed by `Int.negSucc k + 1`. -/
private noncomputable def rowAbove : (k : ℕ) → Row r₁ r₃ (Int.negSucc k + 1)
  | 0 => posRow r₁ r₃ f g hfg hS 0
  | k + 1 => (nonempty_backward (rowAbove k)).some.1

/-- The row in each degree. -/
@[reducible] private noncomputable def row : (n : ℤ) → Row r₁ r₃ n
  | .ofNat k => posRow r₁ r₃ f g hfg hS k
  | .negSucc k => (nonempty_backward (rowAbove r₁ r₃ f g hfg hS k)).some.1

/-- The step from each degree to the next. -/
private noncomputable def block : (n : ℤ) →
    Block r₁ r₃ n (row r₁ r₃ f g hfg hS n) (row r₁ r₃ f g hfg hS (n + 1))
  | .ofNat k => (nonempty_forward (posRow r₁ r₃ f g hfg hS k)).some.2
  | .negSucc 0 => (nonempty_backward (rowAbove r₁ r₃ f g hfg hS 0)).some.2
  | .negSucc (k + 1) => (nonempty_backward (rowAbove r₁ r₃ f g hfg hS (k + 1))).some.2

/-- The middle complete resolution of the horseshoe. -/
@[reducible] private noncomputable def middle : E.CompleteResolution where
  Z n := (row r₁ r₃ f g hfg hS n).Z
  X n := (block r₁ r₃ f g hfg hS n).M
  ι n := (block r₁ r₃ f g hfg hS n).b
  π n := (block r₁ r₃ f g hfg hS n).c
  ι_π n := (block r₁ r₃ f g hfg hS n).b_c
  conflation n := (block r₁ r₃ f g hfg hS n).conflation
  projectiveInjective n := by
    obtain ⟨sp⟩ := (block r₁ r₃ f g hfg hS n).split
    rw [E.projectiveInjective_iff]
    exact ⟨E.isProjective.prop_of_iso sp.isoBinaryBiproduct.symm
        (E.isProjective_biprod (r₁.isProjective_X n) (r₃.isProjective_X n)),
      E.isInjective.prop_of_iso sp.isoBinaryBiproduct.symm
        (E.isInjective_biprod (r₁.isInjective_X n) (r₃.isInjective_X n))⟩

private theorem middle_ι (n : ℤ) :
    (middle r₁ r₃ f g hfg hS).ι n = (block r₁ r₃ f g hfg hS n).b := rfl

private theorem middle_π (n : ℤ) :
    (middle r₁ r₃ f g hfg hS).π n = (block r₁ r₃ f g hfg hS n).c := rfl

/-- The map from the first complete resolution to the middle one. -/
private noncomputable def middleι : r₁.complex ⟶ (middle r₁ r₃ f g hfg hS).complex where
  f n := (block r₁ r₃ f g hfg hS n).left
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [complex_d, complex_d, d_def, d_def]
    have h : (block r₁ r₃ f g hfg hS i).left ≫ (block r₁ r₃ f g hfg hS i).c ≫
        (block r₁ r₃ f g hfg hS (i + 1)).b =
          (r₁.π i ≫ r₁.ι (i + 1)) ≫ (block r₁ r₃ f g hfg hS (i + 1)).left := by
      rw [reassoc_of% (block r₁ r₃ f g hfg hS i).left_c, (block r₁ r₃ f g hfg hS (i + 1)).v_b,
        Category.assoc]
    rw [middle_π, middle_ι]
    exact h

/-- The map from the middle complete resolution to the third one. -/
private noncomputable def middleπ : (middle r₁ r₃ f g hfg hS).complex ⟶ r₃.complex where
  f n := (block r₁ r₃ f g hfg hS n).right
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [complex_d, complex_d, d_def, d_def]
    have h : (block r₁ r₃ f g hfg hS i).right ≫ r₃.π i ≫ r₃.ι (i + 1) =
        ((block r₁ r₃ f g hfg hS i).c ≫ (block r₁ r₃ f g hfg hS (i + 1)).b) ≫
          (block r₁ r₃ f g hfg hS (i + 1)).right := by
      rw [Category.assoc, (block r₁ r₃ f g hfg hS (i + 1)).b_right,
        reassoc_of% (block r₁ r₃ f g hfg hS i).c_w]
    rw [middle_π, middle_ι]
    exact h

variable {r₁ r₃} in
/-- A **horseshoe of complete resolutions** over a conflation `r₁.Z 0 ↪ X₂ ↠ r₃.Z 0`: a complete
resolution of `X₂` with maps of spliced complexes from the first and to the third resolution,
which split in every degree and restrict to the given conflation on the cycles in degree zero. -/
structure Horseshoe (f : r₁.Z 0 ⟶ X₂) (g : X₂ ⟶ r₃.Z 0) where
  /-- The complete resolution of the middle term. -/
  resolution : E.CompleteResolution
  /-- The identification of its cycles in degree zero with the middle term. -/
  iso : resolution.Z 0 ≅ X₂
  /-- The map from the first complete resolution. -/
  ι : r₁.complex ⟶ resolution.complex
  /-- The map to the third complete resolution. -/
  π : resolution.complex ⟶ r₃.complex
  ι_π : ι ≫ π = 0
  cyclesMap_ι : cyclesMap ι = f ≫ iso.inv
  cyclesMap_π : cyclesMap π = iso.hom ≫ g
  /-- In every degree, the maps form a split short complex. -/
  split (n : ℤ) : Nonempty ((ShortComplex.mk ι π ι_π).map
    (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting

attribute [reassoc (attr := simp)] Horseshoe.ι_π

/-- **The horseshoe lemma for complete resolutions.** A conflation whose outer terms are the
cycles in degree zero of two complete resolutions has a horseshoe of complete resolutions. -/
noncomputable def horseshoe : Horseshoe f g where
  resolution := middle r₁ r₃ f g hfg hS
  iso := Iso.refl X₂
  ι := middleι r₁ r₃ f g hfg hS
  π := middleπ r₁ r₃ f g hfg hS
  ι_π := by
    ext n
    exact (block r₁ r₃ f g hfg hS n).left_right
  cyclesMap_ι := by
    have := (E.isKernelCokernelPair _ ((middle r₁ r₃ f g hfg hS).conflation 0)).mono_f
    rw [← cancel_mono ((middle r₁ r₃ f g hfg hS).ι 0), cyclesMap_ι, Iso.refl_inv,
      Category.comp_id]
    -- The row in degree zero is the given conflation, so its inflation is `f`.
    exact (block r₁ r₃ f g hfg hS 0).v_b.symm
  cyclesMap_π := by
    rw [← cancel_mono (r₃.ι 0), cyclesMap_ι, Iso.refl_hom, Category.id_comp]
    -- The row in degree zero is the given conflation, so its deflation is `g`.
    exact (block r₁ r₃ f g hfg hS 0).b_right
  split n := (block r₁ r₃ f g hfg hS n).split

namespace Horseshoe

variable {r₁ r₃} {f g} (h : Horseshoe f g)
  (σ : ∀ n, ((ShortComplex.mk h.ι h.π h.ι_π).map
    (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting)

/-- The connecting cocycle of a horseshoe in degree zero, restricted to the cycles of the third
resolution and precomposed with `g`, is minus the map obtained by extending the inflation of the
first resolution along `f` through the retraction `σ 0`. This compares the triangle of the
degreewise split sequence with the connecting map of the conflation. -/
theorem g_comp_connecting :
    g ≫ r₃.ι 0 ≫ (σ 0).s ≫ h.resolution.d 0 ≫ (σ (0 + 1)).r =
      -(h.iso.inv ≫ h.resolution.ι 0 ≫ (σ 0).r ≫ r₁.d 0) := by
  have hg : g ≫ r₃.ι 0 = h.iso.inv ≫ h.resolution.ι 0 ≫ h.π.f 0 := by
    calc g ≫ r₃.ι 0 = (h.iso.inv ≫ cyclesMap h.π) ≫ r₃.ι 0 := by
          rw [h.cyclesMap_π, Iso.inv_hom_id_assoc]
      _ = _ := by rw [Category.assoc, CompleteResolution.cyclesMap_ι]
  have hs : h.π.f 0 ≫ (σ 0).s = 𝟙 _ - (σ 0).r ≫ h.ι.f 0 := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact (σ 0).id
  have hd : h.ι.f 0 ≫ h.resolution.d 0 ≫ (σ (0 + 1)).r = r₁.d 0 := by
    have hfr : h.ι.f (0 + 1) ≫ (σ (0 + 1)).r = 𝟙 _ := (σ (0 + 1)).f_r
    rw [reassoc_of% (f_comp_d _ h.ι 0), hfr, Category.comp_id]
  rw [reassoc_of% hg, reassoc_of% hs, Preadditive.sub_comp, Category.assoc, hd]
  simp

end Horseshoe

end CompleteResolution

end ExactStructure

end TauCeti
