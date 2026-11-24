/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Monoidal
public import TauCeti.Topology.UnitInterval.Contractible

/-!
# The unit interval `TopCat.I`

The unit interval `TopCat.I`, as an object of `TopCat`, is contractible. Its midpoint
`TopCat.I.midpoint`, and the self-maps `TopCat.I.firstHalf` and `TopCat.I.secondHalf` which
reparametrize it onto its first and second halves, are the reparametrizations along which the
concatenation of two paths restricts to each of the two paths.
-/

public section

noncomputable section

universe u

namespace TopCat.I

/-- The unit interval `TopCat.I` is contractible. -/
instance : ContractibleSpace I.{u} :=
  homeomorph.contractibleSpace

/-- The midpoint of the unit interval `TopCat.I`. -/
def midpoint : I.{u} :=
  homeomorph.symm ⟨1 / 2, by norm_num, by norm_num⟩

/-- The first half of the interval, as a self-map of `TopCat.I`, along which the concatenation of
two paths restricts to the first path. -/
def firstHalf : I.{u} ⟶ I.{u} :=
  ofHom ⟨fun t ↦ homeomorph.symm ⟨homeomorph t / 2,
    div_nonneg (homeomorph t).property.1 zero_le_two, by linarith [(homeomorph t).property.2]⟩,
        by fun_prop⟩

/-- The second half of the interval, as a self-map of `TopCat.I`, along which the concatenation
of two paths restricts to the second path. -/
def secondHalf : I.{u} ⟶ I.{u} :=
  ofHom ⟨fun t ↦ homeomorph.symm ⟨(homeomorph t + 1) / 2,
    by linarith [(homeomorph t).property.1], by linarith [(homeomorph t).property.2]⟩, by fun_prop⟩

@[simp]
lemma coe_homeomorph_midpoint : (homeomorph midpoint.{u} : ℝ) = 1 / 2 :=
  (rfl)

@[simp]
lemma coe_homeomorph_firstHalf_apply (t : I.{u}) :
    (homeomorph (firstHalf t) : ℝ) = homeomorph t / 2 :=
  (rfl)

@[simp]
lemma coe_homeomorph_secondHalf_apply (t : I.{u}) :
    (homeomorph (secondHalf t) : ℝ) = (homeomorph t + 1) / 2 :=
  (rfl)

@[simp]
lemma firstHalf_zero : firstHalf (0 : I.{u}) = 0 :=
  ext (Subtype.ext (by rw [coe_homeomorph_firstHalf_apply]; simp))

@[simp]
lemma firstHalf_one : firstHalf (1 : I.{u}) = midpoint :=
  ext (Subtype.ext (by rw [coe_homeomorph_firstHalf_apply, coe_homeomorph_midpoint]; simp))

@[simp]
lemma secondHalf_zero : secondHalf (0 : I.{u}) = midpoint :=
  ext (Subtype.ext (by rw [coe_homeomorph_secondHalf_apply, coe_homeomorph_midpoint]; simp))

@[simp]
lemma secondHalf_one : secondHalf (1 : I.{u}) = 1 :=
  ext (Subtype.ext (by rw [coe_homeomorph_secondHalf_apply]; norm_num))

end TopCat.I
