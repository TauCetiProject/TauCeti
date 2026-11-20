/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Basic
public import TauCeti.Data.Finsupp.MapDomain

/-!
# Restricting and extending row-finite twisting cocycles along sets of generators

Let `m` be a row-finite twisting cocycle on a graded set of generators `(P, ind)`, with free
differential graded left module `K_m = P →₀ A` (`TauCeti.RowFiniteTwistingCocycle`).

* If a set `S` of generators is closed under the rows, the row of each generator of `S` only
  involving generators of `S`, the rows of the generators of `S` form a twisting cocycle on `S`
  (`TauCeti.RowFiniteTwistingCocycle.restrict`). Its free module is the differential submodule of
  `K_m` spanned by `S`, through relabelling along the inclusion
  (`TauCeti.RowFiniteTwistingCocycle.restrict_differential_mapDomain`), as a CW subcomplex is
  the union of a set of cells closed under the attaching maps.
* Conversely, a twisting cocycle `m'` on `P'` extends along an injective map `e : P' → P`
  preserving the indices, by relabelling its rows along `e` and giving zero rows to the
  generators outside the image of `e` (`TauCeti.RowFiniteTwistingCocycle.extend`). The free module
  of `m'` is then the differential submodule spanned by the image of `e`.

In both situations `e` (the inclusion of `S`, or the given map) carries the row of each generator
of `P'` to the row of its image. For a map `g` from the generators of `P` to a differential
module, the relative cycles of `g ∘ e` on `K_{m'}` are then relative boundaries exactly when
this holds for the relative cycles of `g` on the vectors of `K_m` supported on the image of `e`
(`TauCeti.RowFiniteTwistingCocycle.forall_exists_iff_forall_mem_supported_exists`). This is
how a quasi-isomorphism property proved for a cocycle on a set of generators is transported to,
and from, the vectors supported on that set inside a larger free module.

## Main definitions

* `TauCeti.RowFiniteTwistingCocycle.restrict`: the subcocycle on a set of generators closed under
  the rows.
* `TauCeti.RowFiniteTwistingCocycle.extend`: the extension of a cocycle along an injective,
  index-preserving map of generators, with zero rows off its image.

## Main results

* `TauCeti.RowFiniteTwistingCocycle.restrict_differential_mapDomain`,
  `TauCeti.RowFiniteTwistingCocycle.extend_differential_mapDomain`: the free modules are
  differential submodules.
* `TauCeti.RowFiniteTwistingCocycle.forall_exists_iff_forall_mem_supported_exists`: transport of
  relative boundaries along an injective map of generators compatible with the rows.
-/

public section

open Finsupp Function

namespace TauCeti

universe uR uA uM uP uP'

variable {R : Type uR} {A : Type uA} {P : Type uP} {P' : Type uP'}
  [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {ind : P → ℤ} {ind' : P' → ℤ}

namespace RowFiniteTwistingCocycle

variable (m : RowFiniteTwistingCocycle 𝒜 d P ind)

section Restrict

variable (S : Set P) (hS : ∀ x ∈ S, ∀ y ∈ (m.m x).support, y ∈ S)

include hS

/-- **The subcocycle on a set of generators closed under the rows.** If the row of every
generator of `S` only involves generators of `S`, the rows of the generators of `S` form a
twisting cocycle on `S`, with the same indices. -/
noncomputable def restrict : RowFiniteTwistingCocycle 𝒜 d S fun x ↦ ind x where
  m x := (m.m x).comapDomain ((↑) : S → P) Subtype.val_injective.injOn
  mem_graded x y := by simpa using m.mem_graded x y
  twisting x := by
    refine (mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero _
      fun y ↦ by simpa using m.mem_graded x y).mpr ?_
    -- Relabelled along the inclusion, the restricted rows are the rows of `m`.
    have hrow (y : S) : mapDomain ((↑) : S → P)
        ((m.m y).comapDomain ((↑) : S → P) Subtype.val_injective.injOn) = m.m y :=
      mapDomain_comapDomain _ Subtype.val_injective _ fun z hz ↦ ⟨⟨z, hS y y.2 z hz⟩, rfl⟩
    refine mapDomain_injective Subtype.val_injective ?_
    rw [← rowFiniteTwistedDifferential_mapDomain _ _ fun y ↦ (hrow y).symm, hrow,
      m.differential_row, mapDomain_zero]

/-- The coefficients of the row of a generator of `S` in the subcocycle are its coefficients in
`m`. -/
@[simp]
theorem restrict_m_apply (x y : S) : (m.restrict S hS).m x y = m.m x y :=
  (rfl)

/-- Relabelling the row of a generator of `S` in the subcocycle along the inclusion gives its row
in `m`. -/
@[simp]
theorem mapDomain_restrict_m (x : S) : mapDomain ((↑) : S → P) ((m.restrict S hS).m x) = m.m x :=
  mapDomain_comapDomain _ Subtype.val_injective _ fun y hy ↦ ⟨⟨y, hS x x.2 y hy⟩, rfl⟩

/-- The free module of the subcocycle is a differential submodule: relabelling along the
inclusion commutes with the differentials. -/
theorem restrict_differential_mapDomain (f : S →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m (mapDomain ((↑) : S → P) f) =
      mapDomain ((↑) : S → P)
        (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (m.restrict S hS).m f) :=
  rowFiniteTwistedDifferential_mapDomain _ _ (fun x ↦ (m.mapDomain_restrict_m S hS x).symm) f

end Restrict

section Extend

variable (m' : RowFiniteTwistingCocycle 𝒜 d P' ind') {e : P' → P} (he : Injective e)
  (hind : ∀ z, ind (e z) = ind' z)

/-- The rows of the extension along `e`. -/
private noncomputable def extendRows : P → P →₀ A :=
  Function.extend e (fun z ↦ mapDomain e (m'.m z)) 0

omit [GradedAlgebra 𝒜] in
include he in
private theorem extendRows_apply (z : P') : extendRows m' (e := e) (e z) = mapDomain e (m'.m z) :=
  he.extend_apply _ _ z

omit [GradedAlgebra 𝒜] in
include he hind in
private theorem extendRows_mem_graded (x y : P) :
    extendRows m' (e := e) x y ∈ 𝒜 (ind y - ind x + 1) := by
  classical
  by_cases hx : ∃ z, e z = x
  · obtain ⟨z, rfl⟩ := hx
    rw [extendRows_apply m' he]
    by_cases hy : ∃ w, e w = y
    · obtain ⟨w, rfl⟩ := hy
      rw [mapDomain_apply_of_injective he, hind, hind]
      exact m'.mem_graded z w
    · rw [mapDomain_of_notMem_range _ _ (by simpa using hy)]
      exact zero_mem _
  · simp only [extendRows, Function.extend_apply' _ _ _ hx, Pi.zero_apply, coe_zero]
    exact zero_mem _

/-- **Extending a cocycle along an injective map of generators.** For an injective map
`e : P' → P` preserving the indices, the rows of a twisting cocycle `m'` on `P'`, relabelled
along `e`, together with zero rows on the generators outside the image of `e`, form a twisting
cocycle on `P`. -/
noncomputable def extend (m' : RowFiniteTwistingCocycle 𝒜 d P' ind') (he : Injective e)
    (hind : ∀ z, ind (e z) = ind' z) : RowFiniteTwistingCocycle 𝒜 d P ind where
  m := extendRows m' (e := e)
  mem_graded := extendRows_mem_graded m' he hind
  twisting x := by
    refine (mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero _
      (extendRows_mem_graded m' he hind x)).mpr ?_
    by_cases hx : ∃ z, e z = x
    · obtain ⟨z, rfl⟩ := hx
      rw [extendRows_apply m' he,
        rowFiniteTwistedDifferential_mapDomain e m'.m (extendRows_apply m' he), m'.differential_row,
        mapDomain_zero]
    · simp [extendRows, Function.extend_apply' _ _ _ hx]

/-- The row of the image of a generator of `P'` is its row in `m'`, relabelled along `e`. -/
@[simp]
theorem extend_m_apply (z : P') : (m'.extend he hind).m (e z) = mapDomain e (m'.m z) :=
  extendRows_apply m' he z

/-- A generator outside the image of `e` has zero row. -/
theorem extend_m_of_notMem_range {x : P} (hx : x ∉ Set.range e) : (m'.extend he hind).m x = 0 :=
  Function.extend_apply' (f := e) (fun z ↦ mapDomain e (m'.m z)) 0 x hx

/-- The free module of `m'` is a differential submodule of that of its extension: relabelling
along `e` commutes with the differentials. -/
@[simp]
theorem extend_differential_mapDomain (f : P' →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (m'.extend he hind).m (mapDomain e f) =
      mapDomain e (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m'.m f) :=
  rowFiniteTwistedDifferential_mapDomain e m'.m (m'.extend_m_apply he hind) f

end Extend

section Transport

variable {M : Type uM} [AddCommGroup M] [Module R M] [Module A M] {dM : M →ₗ[R] M}
  (m' : RowFiniteTwistingCocycle 𝒜 d P' ind') {e : P' → P} (he : Injective e)
  (hm : ∀ z, m.m (e z) = mapDomain e (m'.m z)) (g : P → M) (N : Submodule A M)

include he hm in
/-- **Relative boundaries along an injective map of generators.** Let `e : P' → P` be injective
and carry the row of each generator of `P'` in `m'` to the row of its image in `m`, and let `N`
be a submodule of a differential module `M`. The relative cycles of `g ∘ e : K_{m'} → M`, with
target in `N`, are relative boundaries with target in `N` exactly when the same holds for the
relative cycles of `g : K_m → M` supported on the image of `e`, with relative boundaries
supported on the image of `e`. -/
theorem forall_exists_iff_forall_mem_supported_exists :
    (∀ (u : P' →₀ A) (w : M), rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m'.m u = 0 →
      linearCombination A (g ∘ e) u = dM w → w ∈ N → ∃ (u' : P' →₀ A) (w' : M), w' ∈ N ∧
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m'.m u' = u ∧
          linearCombination A (g ∘ e) u' + dM w' = w) ↔
    ∀ (u : P →₀ A) (w : M), u ∈ supported A A (Set.range e) →
      rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m u = 0 →
      linearCombination A g u = dM w → w ∈ N → ∃ (u' : P →₀ A) (w' : M),
        u' ∈ supported A A (Set.range e) ∧ w' ∈ N ∧
          rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m u' = u ∧
            linearCombination A g u' + dM w' = w := by
  have hD (f : P' →₀ A) := rowFiniteTwistedDifferential_mapDomain (𝒜 := 𝒜) (d := d) e m'.m hm f
  have hinj := mapDomain_injective (M := A) he
  constructor
  · intro H u w hu hDu hgu hw
    obtain ⟨u₀, rfl⟩ := (mem_supported_range_iff e u).1 hu
    rw [hD, ← mapDomain_zero (f := e)] at hDu
    rw [linearCombination_mapDomain] at hgu
    obtain ⟨u₀', w', hw', hDu₀', hgu₀'⟩ := H u₀ w (hinj hDu) hgu hw
    refine ⟨mapDomain e u₀', w', (mem_supported_range_iff e _).2 ⟨u₀', rfl⟩,
      hw', by rw [hD, hDu₀'], by rwa [linearCombination_mapDomain]⟩
  · intro H u w hDu hgu hw
    obtain ⟨u', w', hu', hw', hDu', hgu'⟩ := H (mapDomain e u) w
      ((mem_supported_range_iff e _).2 ⟨u, rfl⟩)
      (by rw [hD, hDu, mapDomain_zero]) (by rwa [linearCombination_mapDomain]) hw
    obtain ⟨u₀', rfl⟩ := (mem_supported_range_iff e u').1 hu'
    refine ⟨u₀', w', hw', hinj (by rw [← hD, hDu']), by rwa [linearCombination_mapDomain] at hgu'⟩

end Transport

end RowFiniteTwistingCocycle

end TauCeti
