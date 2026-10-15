/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Normalized

/-!
# Eisenstein subspaces with fixed nebentypus

For weight `k >= 3`, the Eisenstein subspace of `M_k(N, chi)` is spanned by the raised
character Eisenstein series

`E_k^(psi, phi, t) = V_t E_k^(psi, phi)`

with primitive characters `psi` and `phi`, compatible parity, `t * u * v | N`, and induced
nebentypus `chi`. This file packages the exact indexing data and defines the span inside the
already existing character space. In particular, character-space membership is built into each
generator rather than imposed afterwards on the span.

The resulting subspace is the Eisenstein term in the cusp--Eisenstein decomposition. Its
comparison with the image of the constant-term map is separate: it requires the spanning and
linear-independence theorem for the constant terms at all cusps.

## Main definitions

* `TauCeti.EisensteinSeries.CharIndex`: the primitive, parity-compatible data `(psi, phi, t)`
  indexing a raised character Eisenstein series at level `N`.
* `TauCeti.EisensteinSeries.CharIndex.nebentypus`: the product character induced at level `N`.
* `TauCeti.EisensteinSeries.CharIndex.form`: the corresponding normalized raised series.
* `TauCeti.eisensteinSubspace`: the span of the generators with prescribed nebentypus.

## Main results

* `TauCeti.EisensteinSeries.CharIndex.form_mem_modFormCharSpace`: every indexed series belongs
  to the character space prescribed by its induced nebentypus.
* `TauCeti.mem_eisensteinSubspace`: every prescribed-nebentypus generator belongs to the
  Eisenstein subspace.
* `TauCeti.mem_eisensteinSubspace_iff`: membership is equivalent to being a finite linear
  combination of the prescribed-nebentypus generators.
* `TauCeti.eisensteinSubspace_le`: the elimination rule for the span.
* `TauCeti.eisensteinSubspace_ne_bot_iff`: the subspace is nonzero exactly when its indexing
  type is inhabited.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Section 4.5.
* [T. Miyake, *Modular forms*][miyake1989], Section 7.1.
-/

public noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups

namespace TauCeti.EisensteinSeries

/-- The data indexing a normalized raised character Eisenstein series of weight `k` and level
`N`: primitive characters `psi` modulo `u` and `phi` modulo `v`, compatible parity, and a
raising parameter `t` with `tuv | N`.

The induced character at level `N` is kept as a derived accessor, since it is canonically
determined by this data. -/
structure CharIndex (N k : ℕ) where
  /-- The modulus of the first primitive character. -/
  u : ℕ
  /-- The modulus of the second primitive character. -/
  v : ℕ
  /-- The level-raising parameter. -/
  t : ℕ
  /-- The first primitive Dirichlet character. -/
  psi : DirichletCharacter ℂ u
  /-- The second primitive Dirichlet character. -/
  phi : DirichletCharacter ℂ v
  /-- The first character is primitive. -/
  psi_primitive : psi.IsPrimitive
  /-- The second character is primitive. -/
  phi_primitive : phi.IsPrimitive
  /-- The two characters have the parity required in weight `k`. -/
  parity : psi (-1) * phi (-1) = (-1) ^ (k : ℤ)
  /-- The natural level `tuv` divides the target level. -/
  level_dvd : t * (u * v) ∣ N

namespace CharIndex

variable {N k : ℕ} (a : CharIndex N k)

/-- The product nebentypus of an Eisenstein index, with both primitive characters raised to the
target level `N`. -/
def nebentypus : (ZMod N)ˣ →* ℂˣ :=
  (a.psi.changeLevel ((dvd_mul_right a.u a.v).trans
      ((dvd_mul_left (a.u * a.v) a.t).trans a.level_dvd)) *
    a.phi.changeLevel ((dvd_mul_left a.v a.u).trans
      ((dvd_mul_left (a.u * a.v) a.t).trans a.level_dvd))).toUnitHom

/-- The defining expression for the nebentypus of an Eisenstein index. -/
theorem nebentypus_def :
    a.nebentypus =
      (a.psi.changeLevel ((dvd_mul_right a.u a.v).trans
          ((dvd_mul_left (a.u * a.v) a.t).trans a.level_dvd)) *
        a.phi.changeLevel ((dvd_mul_left a.v a.u).trans
          ((dvd_mul_left (a.u * a.v) a.t).trans a.level_dvd))).toUnitHom :=
  by
    unfold nebentypus
    congr

/-- The normalized raised character Eisenstein series attached to an index. -/
def form [NeZero N] (hk : 3 ≤ (k : ℤ)) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) (k : ℤ) :=
  normalizedCharEisensteinSeriesMFRaise a.psi a.phi a.t hk a.level_dvd

/-- The defining expression for the normalized raised series attached to an Eisenstein index. -/
theorem form_def [NeZero N] (hk : 3 ≤ (k : ℤ)) :
    a.form hk = normalizedCharEisensteinSeriesMFRaise a.psi a.phi a.t hk a.level_dvd :=
  by
    unfold form
    congr

/-- An indexed Eisenstein series belongs to the character space of its induced nebentypus. -/
theorem form_mem_modFormCharSpace [NeZero N] (hk : 3 ≤ (k : ℤ)) :
    a.form hk ∈ modFormCharSpace (k : ℤ) a.nebentypus := by
  exact normalizedCharEisensteinSeriesMFRaise_mem_modFormCharSpace
    a.psi a.phi hk a.level_dvd

/-- The coefficient at the first positive supported index `t` of an indexed Eisenstein series
is `1`. -/
@[simp]
theorem qExpansion_form_coeff_t [NeZero N] (hk : 3 ≤ (k : ℤ)) :
    (qExpansion 1 (a.form hk)).coeff a.t = 1 :=
  qExpansion_normalizedCharEisensteinSeriesMFRaise_coeff_self
    a.psi a.phi hk a.level_dvd a.parity a.phi_primitive

/-- Every indexed Eisenstein series is nonzero. -/
theorem form_ne_zero [NeZero N] (hk : 3 ≤ (k : ℤ)) : a.form hk ≠ 0 :=
  normalizedCharEisensteinSeriesMFRaise_ne_zero
    a.psi a.phi hk a.level_dvd a.parity a.phi_primitive

variable {chi : (ZMod N)ˣ →* ℂˣ}

/-- An indexed Eisenstein series, regarded as an element of a specified character space whose
character agrees with the induced nebentypus. -/
def inCharSpace [NeZero N] (hk : 3 ≤ (k : ℤ)) (hchi : a.nebentypus = chi) :
    modFormCharSpace (k : ℤ) chi :=
  ⟨a.form hk, hchi ▸ a.form_mem_modFormCharSpace hk⟩

/-- Coercing `inCharSpace` forgets only the proof of character-space membership. -/
@[simp]
theorem coe_inCharSpace [NeZero N] (hk : 3 ≤ (k : ℤ)) (hchi : a.nebentypus = chi) :
    (a.inCharSpace hk hchi : ModularForm ((Gamma1 N).map (mapGL ℝ)) (k : ℤ)) =
      a.form hk :=
  (rfl)

/-- An indexed Eisenstein series remains nonzero inside its character space. -/
theorem inCharSpace_ne_zero [NeZero N] (hk : 3 ≤ (k : ℤ))
    (hchi : a.nebentypus = chi) : a.inCharSpace hk hchi ≠ 0 := by
  intro h
  apply a.form_ne_zero hk
  exact congrArg Subtype.val h

end CharIndex

end TauCeti.EisensteinSeries

namespace TauCeti

open TauCeti.EisensteinSeries

variable {N k : ℕ} [NeZero N] (chi : (ZMod N)ˣ →* ℂˣ)

/-- The **Eisenstein subspace** of `M_k(N, chi)` for `k >= 3`: the span of the normalized raised
series `E_k^(psi, phi, t)` over primitive, parity-compatible pairs whose induced nebentypus is
`chi` and whose natural level `tuv` divides `N`. -/
def eisensteinSubspace (hk : 3 ≤ (k : ℤ)) :
    Submodule ℂ (modFormCharSpace (k : ℤ) chi) :=
  Submodule.span ℂ (Set.range fun a : {a : CharIndex N k // a.nebentypus = chi} ↦
    a.1.inCharSpace hk a.2)

/-- The defining span of the Eisenstein subspace. -/
theorem eisensteinSubspace_def (hk : 3 ≤ (k : ℤ)) :
    eisensteinSubspace chi hk =
      Submodule.span ℂ (Set.range fun a : {a : CharIndex N k // a.nebentypus = chi} ↦
        a.1.inCharSpace hk a.2) :=
  (rfl)

/-- Every indexed series with induced nebentypus `chi` belongs to the Eisenstein subspace. -/
theorem mem_eisensteinSubspace (hk : 3 ≤ (k : ℤ)) (a : CharIndex N k)
    (hchi : a.nebentypus = chi) : a.inCharSpace hk hchi ∈ eisensteinSubspace chi hk := by
  rw [eisensteinSubspace_def]
  exact Submodule.subset_span ⟨⟨a, hchi⟩, rfl⟩

/-- A form belongs to the Eisenstein subspace exactly when it is a finite linear combination of
the indexed series with induced nebentypus `chi`. -/
theorem mem_eisensteinSubspace_iff (hk : 3 ≤ (k : ℤ))
    (f : modFormCharSpace (k : ℤ) chi) :
    f ∈ eisensteinSubspace chi hk ↔
      ∃ c : {a : CharIndex N k // a.nebentypus = chi} →₀ ℂ,
        c.sum (fun a z ↦ z • a.1.inCharSpace hk a.2) = f := by
  rw [eisensteinSubspace_def]
  exact Finsupp.mem_span_range_iff_exists_finsupp

/-- Elimination rule for the Eisenstein subspace: a subspace containing every indexed series of
nebentypus `chi` contains their span. -/
theorem eisensteinSubspace_le (hk : 3 ≤ (k : ℤ))
    {V : Submodule ℂ (modFormCharSpace (k : ℤ) chi)}
    (hV : ∀ (a : CharIndex N k) (hchi : a.nebentypus = chi),
      a.inCharSpace hk hchi ∈ V) : eisensteinSubspace chi hk ≤ V := by
  rw [eisensteinSubspace_def, Submodule.span_le]
  rintro _ ⟨⟨a, hchi⟩, rfl⟩
  exact hV a hchi

/-- The Eisenstein subspace is nonzero exactly when there is at least one primitive,
parity-compatible raised Eisenstein series with the prescribed nebentypus. -/
theorem eisensteinSubspace_ne_bot_iff (hk : 3 ≤ (k : ℤ)) :
    eisensteinSubspace chi hk ≠ ⊥ ↔
      Nonempty {a : CharIndex N k // a.nebentypus = chi} := by
  constructor
  · contrapose!
    intro h
    rw [eisensteinSubspace_def]
    let _ : IsEmpty {a : CharIndex N k // a.nebentypus = chi} := h
    simp
  · rintro ⟨⟨a, hchi⟩⟩ hbot
    have hmem := mem_eisensteinSubspace chi hk a hchi
    rw [hbot] at hmem
    exact a.inCharSpace_ne_zero hk hchi ((Submodule.mem_bot ℂ).mp hmem)

end TauCeti
