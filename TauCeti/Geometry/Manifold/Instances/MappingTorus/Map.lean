/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.MappingTorus

/-!
# Maps of smooth mapping tori

Let `φ : M ≃ₘ^n⟮I, I⟯ M` and `ψ : N ≃ₘ^n⟮J, J⟯ N` be diffeomorphisms, with smooth mapping tori
`Y_φ` and `Y_ψ` (`TauCeti.SmoothMappingTorus`). A time-dependent family of maps `g t : M → N`
satisfying the equivariance

`ψ ∘ g (t + 1) = g t ∘ φ`

induces the map `[t, x] ↦ [t, g t x]` of mapping tori
(`TauCeti.SmoothMappingTorus.mapFamily φ ψ g h`). It lies over the circle, and it is `C^n` when
`(t, x) ↦ g t x` is. A family of diffeomorphisms whose inverses are also jointly `C^n` induces a
diffeomorphism `Y_φ ≃ Y_ψ` (`TauCeti.SmoothMappingTorus.congrFamily`).

For a constant family the equivariance says that `g : M → N` intertwines `φ` and `ψ`,
`g ∘ φ = ψ ∘ g`, and the induced map is

`[t, x] ↦ [t, g x]`

(`TauCeti.SmoothMappingTorus.map φ ψ g h`). Unlike the maps induced by general families, it also
intertwines the two suspension flows. Maps of mapping tori are functorial in `g`.

A diffeomorphism `e : M ≃ₘ^n⟮I, J⟯ N` with `e ∘ φ = ψ ∘ e`, a *conjugacy* from `φ` to `ψ`,
induces a diffeomorphism `Y_φ ≃ Y_ψ` (`TauCeti.SmoothMappingTorus.congr e h`). For example
`e` conjugates `φ` to `e ∘ φ ∘ e⁻¹`, so conjugate diffeomorphisms have diffeomorphic mapping tori,
by a diffeomorphism over the circle that intertwines the suspension flows and sends the fibre
inclusion `x ↦ [t, x]` to `y ↦ [t, y]` after `e`.

The induced maps agree with those of Tau Ceti's topological mapping torus `TauCeti.MappingTorus`
under the homeomorphisms `TauCeti.SmoothMappingTorus.homeomorphMappingTorus`.

## Main definitions

* `TauCeti.SmoothMappingTorus.mapFamily φ ψ g h`: the map `[t, x] ↦ [t, g t x]` induced by an
  equivariant family `g`.
* `TauCeti.SmoothMappingTorus.congrFamily e he he' h`: the diffeomorphism induced by an equivariant
  jointly smooth family of diffeomorphisms `e`.
* `TauCeti.SmoothMappingTorus.map φ ψ g h`: the map `[t, x] ↦ [t, g x]` of mapping tori induced by
  a map `g` intertwining `φ` and `ψ`.
* `TauCeti.SmoothMappingTorus.congr e h`: the diffeomorphism of mapping tori induced by a
  diffeomorphism `e` conjugating `φ` to `ψ`.

## Main results

* `TauCeti.SmoothMappingTorus.mapFamily_mk`, `TauCeti.SmoothMappingTorus.proj_mapFamily`: the
  map induced by a family sends `[t, x]` to `[t, g t x]` and lies over the circle.
* `TauCeti.SmoothMappingTorus.mapFamily_id`, `TauCeti.SmoothMappingTorus.mapFamily_mapFamily`:
  functoriality in the family.
* `TauCeti.SmoothMappingTorus.contMDiff_mapFamily`: the induced map is `C^n` when the family is.
* `TauCeti.SmoothMappingTorus.congrFamily_refl`, `TauCeti.SmoothMappingTorus.congrFamily_symm`,
  `TauCeti.SmoothMappingTorus.congrFamily_trans`: the diffeomorphisms induced by families respect
  identities, inverses and composition.
* `TauCeti.SmoothMappingTorus.map_mk`, `TauCeti.SmoothMappingTorus.proj_map`,
  `TauCeti.SmoothMappingTorus.map_flow`: the induced map sends `[t, x]` to `[t, g x]`, lies over
  the circle and intertwines the suspension flows.
* `TauCeti.SmoothMappingTorus.map_id`, `TauCeti.SmoothMappingTorus.map_map`: functoriality.
* `TauCeti.SmoothMappingTorus.contMDiff_map`: the induced map is `C^n` when `g` is.
* `TauCeti.SmoothMappingTorus.homeomorphMappingTorus_map`: comparison with the maps of
  topological mapping tori.
* `TauCeti.SmoothMappingTorus.congr_refl`, `TauCeti.SmoothMappingTorus.congr_symm`,
  `TauCeti.SmoothMappingTorus.congr_trans`: the induced diffeomorphisms respect identities,
  inverses and composition of conjugacies.

## References

* Allen Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2 (mapping
  tori).
-/

public noncomputable section

open Function
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothMappingTorus

open Cover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] {H'' : Type*}
  [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''} {P : Type*} [TopologicalSpace P]
  [ChartedSpace H'' P] {n : ℕ∞ω}

/-! ### Maps induced by equivariant families -/

section MapFamily

variable (φ : M ≃ₘ^n⟮I, I⟯ M) (ψ : N ≃ₘ^n⟮J, J⟯ N) (g : ℝ → M → N)
  (h : ∀ t x, ψ (g (t + 1) x) = g t (φ x))

include h in
/-- The equivariance `ψ ∘ g (t + 1) = g t ∘ φ` extends to all integer shifts:
`ψ ^ k ∘ g (t + k) = g t ∘ φ ^ k`. -/
private theorem zpow_apply_add_intCast (k : ℤ) (t : ℝ) (x : M) :
    (ψ ^ k) (g (t + k) x) = g t ((φ ^ k) x) := by
  induction k using Int.induction_on generalizing t x with
  | zero => simp
  | succ k ih =>
    push_cast at ih ⊢
    simp only [zpow_add_one, Diffeomorph.mul_apply, ← add_assoc, h, ih]
  | pred k ih =>
    -- One step of the equivariance backwards: `ψ⁻¹ ∘ g s = g (s + 1) ∘ φ⁻¹`.
    have h' (s : ℝ) (y : M) : ψ⁻¹ (g s y) = g (s + 1) (φ⁻¹ y) := by
      rw [Diffeomorph.inv_apply, Diffeomorph.inv_apply, ← ψ.symm_apply_apply (g (s + 1) _), h,
        φ.apply_symm_apply]
    push_cast at ih ⊢
    simp only [zpow_sub_one, Diffeomorph.mul_apply, h', ← ih, add_assoc, sub_add_cancel]

/-- The map `[t, x] ↦ [t, g t x]` of mapping tori induced by a family of maps `g t : M → N`
satisfying the equivariance `ψ ∘ g (t + 1) = g t ∘ φ`. It is well defined because the
equivariance extends to all integer shifts of time. For a constant family it is the map
`TauCeti.SmoothMappingTorus.map`. -/
def mapFamily : SmoothMappingTorus φ → SmoothMappingTorus ψ :=
  MulAction.orbitRelQuotientLift
    (fun z ↦ mk ψ ((ofProd φ).symm z).1 (g ((ofProd φ).symm z).1 ((ofProd φ).symm z).2))
    fun k z ↦ by
      rw [ofProd_symm_smul, mk_add_intCast, zpow_apply_add_intCast φ ψ g h]
      simp

/-- The induced map sends `[t, x]` to `[t, g t x]`. -/
@[simp]
theorem mapFamily_mk (t : ℝ) (x : M) : mapFamily φ ψ g h (mk φ t x) = mk ψ t (g t x) := by
  rw [mapFamily, mk_def φ, MulAction.orbitRelQuotientLift_mk, Equiv.symm_apply_apply]

/-- On `ℝ × M`, the induced map is `(t, x) ↦ (t, g t x)` followed by the quotient map of `Y_ψ`. -/
theorem mapFamily_comp_uncurry_mk :
    mapFamily φ ψ g h ∘ uncurry (mk φ) = uncurry (mk ψ) ∘ fun p : ℝ × M ↦ (p.1, g p.1 p.2) :=
  funext fun p ↦ mapFamily_mk φ ψ g h p.1 p.2

/-- The induced map lies over the circle. -/
@[simp]
theorem proj_mapFamily (z : SmoothMappingTorus φ) : proj ψ (mapFamily φ ψ g h z) = proj φ z := by
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
  simp

/-- The induced map lies over the circle, as an equality of functions. -/
theorem proj_comp_mapFamily : proj ψ ∘ mapFamily φ ψ g h = proj φ :=
  funext (proj_mapFamily φ ψ g h)

/-- The constant family of identity maps induces the identity of the mapping torus. -/
@[simp]
theorem mapFamily_id : mapFamily φ φ (fun _ ↦ id) (fun _ _ ↦ rfl) = id := by
  funext z
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
  simp

/-- Maps induced by equivariant families respect composition of the families. -/
@[simp]
theorem mapFamily_mapFamily (χ : P ≃ₘ^n⟮K, K⟯ P) (g' : ℝ → N → P)
    (h' : ∀ t y, χ (g' (t + 1) y) = g' t (ψ y)) (z : SmoothMappingTorus φ) :
    mapFamily ψ χ g' h' (mapFamily φ ψ g h z) =
      mapFamily φ χ (fun t ↦ g' t ∘ g t) (fun t x ↦ by simp only [comp_apply, h', h]) z := by
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
  simp

/-- The induced map is continuous when `(t, x) ↦ g t x` is. -/
theorem continuous_mapFamily (hg : Continuous fun p : ℝ × M ↦ g p.1 p.2) :
    Continuous (mapFamily φ ψ g h) :=
  continuous_orbitRelQuotientLift_iff.2 <| (continuous_uncurry_mk ψ).comp
    ((continuous_ofProd_symm φ).fst.prodMk (hg.comp (continuous_ofProd_symm φ)))

/-- The induced map is `C^n` when `(t, x) ↦ g t x` is. -/
theorem contMDiff_mapFamily [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] [T2Space N]
    [LocallyCompactSpace N] [IsManifold J n N]
    (hg : ContMDiff (𝓘(ℝ).prod I) J n fun p : ℝ × M ↦ g p.1 p.2) :
    ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod J) n (mapFamily φ ψ g h) := by
  rw [← (isLocalDiffeomorph_uncurry_mk φ).contMDiff_comp_iff (uncurry_mk_surjective φ) le_rfl,
    mapFamily_comp_uncurry_mk]
  exact (contMDiff_uncurry_mk ψ).comp (contMDiff_fst.prodMk hg)

end MapFamily

/-! ### The map induced by an intertwining map -/

section Map

variable (φ : M ≃ₘ^n⟮I, I⟯ M) (ψ : N ≃ₘ^n⟮J, J⟯ N) (g : M → N) (h : Semiconj g φ ψ)

/-- The map `[t, x] ↦ [t, g x]` of mapping tori induced by a map `g` intertwining the
diffeomorphisms `φ` and `ψ`, `g ∘ φ = ψ ∘ g`. It is the map induced by the constant family `g`,
for which the equivariance `ψ ∘ g = g ∘ φ` is the intertwining. -/
def map : SmoothMappingTorus φ → SmoothMappingTorus ψ :=
  mapFamily φ ψ (fun _ ↦ g) fun _ x ↦ (h x).symm

/-- The induced map sends `[t, x]` to `[t, g x]`. -/
@[simp]
theorem map_mk (t : ℝ) (x : M) : map φ ψ g h (mk φ t x) = mk ψ t (g x) :=
  mapFamily_mk φ ψ _ _ t x

/-- On `ℝ × M`, the induced map is `(t, x) ↦ (t, g x)` followed by the quotient map of `Y_ψ`. -/
theorem map_comp_uncurry_mk :
    map φ ψ g h ∘ uncurry (mk φ) = uncurry (mk ψ) ∘ Prod.map id g :=
  funext fun p ↦ map_mk φ ψ g h p.1 p.2

/-- The induced map lies over the circle. -/
@[simp]
theorem proj_map (z : SmoothMappingTorus φ) : proj ψ (map φ ψ g h z) = proj φ z :=
  proj_mapFamily φ ψ _ _ z

/-- The induced map lies over the circle, as an equality of functions. -/
theorem proj_comp_map : proj ψ ∘ map φ ψ g h = proj φ :=
  proj_comp_mapFamily φ ψ _ _

/-- The induced map intertwines the suspension flows. -/
@[simp]
theorem map_flow (s : ℝ) (z : SmoothMappingTorus φ) :
    map φ ψ g h (flow φ s z) = flow ψ s (map φ ψ g h z) := by
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
  simp

/-- The induced map sends the fibre inclusion `x ↦ [t, x]` to `y ↦ [t, y]` after `g`. -/
theorem map_comp_mk (t : ℝ) : map φ ψ g h ∘ mk φ t = mk ψ t ∘ g :=
  funext fun x ↦ map_mk φ ψ g h t x

/-- The induced map is continuous when `g` is. -/
theorem continuous_map (hg : Continuous g) : Continuous (map φ ψ g h) :=
  continuous_mapFamily φ ψ _ _ (hg.comp continuous_snd)

/-- The identity of `M` induces the identity of the mapping torus. -/
@[simp]
theorem map_id : map φ φ id (Semiconj.id_left) = id :=
  mapFamily_id φ

/-- Maps of mapping tori respect composition of maps intertwining the monodromies. -/
@[simp]
theorem map_map (χ : P ≃ₘ^n⟮K, K⟯ P) (g' : N → P) (h' : Semiconj g' ψ χ)
    (z : SmoothMappingTorus φ) :
    map ψ χ g' h' (map φ ψ g h z) = map φ χ (g' ∘ g) (h'.comp_left h) z :=
  mapFamily_mapFamily φ ψ _ _ χ _ _ z

/-- The induced map is the map of topological mapping tori induced by `g`, under the
homeomorphisms `TauCeti.SmoothMappingTorus.homeomorphMappingTorus`. -/
theorem homeomorphMappingTorus_map (hg : Continuous g) (z : SmoothMappingTorus φ) :
    homeomorphMappingTorus ψ (map φ ψ g h z) =
      MappingTorus.map φ.toHomeomorph.symm ψ.toHomeomorph.symm ⟨g, hg⟩
        (Semiconj.inverses_right h φ.toEquiv.right_inv ψ.toEquiv.left_inv)
        (homeomorphMappingTorus φ z) := by
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
  simp

/-- The induced map is `C^n` when `g` is. -/
theorem contMDiff_map [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] [T2Space N]
    [LocallyCompactSpace N] [IsManifold J n N] (hg : ContMDiff I J n g) :
    ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod J) n (map φ ψ g h) :=
  contMDiff_mapFamily φ ψ _ _ (hg.comp contMDiff_snd)

end Map

/-! ### Diffeomorphisms induced by equivariant families of diffeomorphisms -/

section CongrFamily

variable {φ : M ≃ₘ^n⟮I, I⟯ M} {ψ : N ≃ₘ^n⟮J, J⟯ N}

/-- The inverses of a family of diffeomorphisms satisfying the equivariance
`ψ ∘ e (t + 1) = e t ∘ φ` satisfy the equivariance `φ ∘ (e (t + 1))⁻¹ = (e t)⁻¹ ∘ ψ` in the
opposite direction. -/
theorem apply_symm_add_one {e : ℝ → M ≃ₘ^n⟮I, J⟯ N}
    (h : ∀ t x, ψ (e (t + 1) x) = e t (φ x)) (t : ℝ) (y : N) :
    φ ((e (t + 1)).symm y) = (e t).symm (ψ y) := by
  have h' := congrArg (e t).symm (h t ((e (t + 1)).symm y))
  rwa [Diffeomorph.apply_symm_apply, Diffeomorph.symm_apply_apply, eq_comm] at h'

variable [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] [T2Space N]
  [LocallyCompactSpace N] [IsManifold J n N]

/-- The diffeomorphism `[t, x] ↦ [t, e t x]` of mapping tori induced by a family of
diffeomorphisms `e t : M ≃ N` satisfying the equivariance `ψ ∘ e (t + 1) = e t ∘ φ`, provided
`(t, x) ↦ e t x` and `(t, y) ↦ (e t)⁻¹ y` are `C^n`. Its inverse is induced by the inverse family
(`TauCeti.SmoothMappingTorus.congrFamily_symm`). -/
def congrFamily (e : ℝ → M ≃ₘ^n⟮I, J⟯ N)
    (he : ContMDiff (𝓘(ℝ).prod I) J n fun p : ℝ × M ↦ e p.1 p.2)
    (he' : ContMDiff (𝓘(ℝ).prod J) I n fun p : ℝ × N ↦ (e p.1).symm p.2)
    (h : ∀ t x, ψ (e (t + 1) x) = e t (φ x)) :
    SmoothMappingTorus φ ≃ₘ^n⟮𝓘(ℝ).prod I, 𝓘(ℝ).prod J⟯ SmoothMappingTorus ψ where
  toFun := mapFamily φ ψ (fun t ↦ e t) h
  invFun := mapFamily ψ φ (fun t ↦ (e t).symm) (apply_symm_add_one h)
  left_inv z := by
    obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
    simp
  right_inv z := by
    obtain ⟨⟨t, y⟩, rfl⟩ := uncurry_mk_surjective ψ z
    simp
  contMDiff_toFun := contMDiff_mapFamily φ ψ (fun t ↦ e t) h he
  contMDiff_invFun := contMDiff_mapFamily ψ φ (fun t ↦ (e t).symm) (apply_symm_add_one h) he'

variable (e : ℝ → M ≃ₘ^n⟮I, J⟯ N)
  (he : ContMDiff (𝓘(ℝ).prod I) J n fun p : ℝ × M ↦ e p.1 p.2)
  (he' : ContMDiff (𝓘(ℝ).prod J) I n fun p : ℝ × N ↦ (e p.1).symm p.2)
  (h : ∀ t x, ψ (e (t + 1) x) = e t (φ x))

/-- The diffeomorphism induced by an equivariant family is the map induced by the family. -/
@[simp]
theorem coe_congrFamily : ⇑(congrFamily e he he' h) = mapFamily φ ψ (fun t ↦ e t) h :=
  (rfl)

/-- The inverse of the diffeomorphism induced by an equivariant family is induced by the inverse
family. -/
@[simp]
theorem congrFamily_symm :
    (congrFamily e he he' h).symm =
      congrFamily (fun t ↦ (e t).symm) he' he (apply_symm_add_one h) :=
  (rfl)

/-- The constant family of identities induces the identity of the mapping torus. -/
@[simp]
theorem congrFamily_refl :
    congrFamily (ψ := φ) (fun _ ↦ Diffeomorph.refl I M n) contMDiff_snd contMDiff_snd
        (fun _ _ ↦ rfl) =
      Diffeomorph.refl (𝓘(ℝ).prod I) (SmoothMappingTorus φ) n :=
  Diffeomorph.ext fun z ↦ congrFun (mapFamily_id φ) z

/-- The diffeomorphisms induced by equivariant families respect composition of the families. -/
@[simp]
theorem congrFamily_trans [T2Space P] [LocallyCompactSpace P] [IsManifold K n P]
    {χ : P ≃ₘ^n⟮K, K⟯ P} (f : ℝ → N ≃ₘ^n⟮J, K⟯ P)
    (hf : ContMDiff (𝓘(ℝ).prod J) K n fun p : ℝ × N ↦ f p.1 p.2)
    (hf' : ContMDiff (𝓘(ℝ).prod K) J n fun p : ℝ × P ↦ (f p.1).symm p.2)
    (h' : ∀ t y, χ (f (t + 1) y) = f t (ψ y)) :
    (congrFamily e he he' h).trans (congrFamily f hf hf' h') =
      congrFamily (fun t ↦ (e t).trans (f t)) (hf.comp (contMDiff_fst.prodMk he))
        (he'.comp (contMDiff_fst.prodMk hf'))
        (fun t x ↦ by simp only [Diffeomorph.coe_trans, comp_apply, h', h]) :=
  Diffeomorph.ext fun z ↦ mapFamily_mapFamily φ ψ (fun t ↦ e t) h χ (fun t ↦ f t) h' z

end CongrFamily

/-! ### Conjugacies -/

section Congr

variable [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] [T2Space N]
  [LocallyCompactSpace N] [IsManifold J n N]
  {φ : M ≃ₘ^n⟮I, I⟯ M} {ψ : N ≃ₘ^n⟮J, J⟯ N}

/-- The diffeomorphism `[t, x] ↦ [t, e x]` of mapping tori induced by a diffeomorphism `e`
conjugating `φ` to `ψ`, `e ∘ φ = ψ ∘ e`. It is the diffeomorphism induced by the constant family
`e`. Its inverse is induced by `e⁻¹` (`TauCeti.SmoothMappingTorus.congr_symm`). -/
def congr (e : M ≃ₘ^n⟮I, J⟯ N) (h : Semiconj e φ ψ) :
    SmoothMappingTorus φ ≃ₘ^n⟮𝓘(ℝ).prod I, 𝓘(ℝ).prod J⟯ SmoothMappingTorus ψ :=
  congrFamily (fun _ ↦ e) (e.contMDiff.comp contMDiff_snd) (e.symm.contMDiff.comp contMDiff_snd)
    fun _ x ↦ (h x).symm

/-- The diffeomorphism induced by a conjugacy `e` is the map induced by `e`. -/
@[simp]
theorem coe_congr (e : M ≃ₘ^n⟮I, J⟯ N) (h : Semiconj e φ ψ) :
    ⇑(congr e h) = map φ ψ e h :=
  (rfl)

/-- The inverse of the diffeomorphism induced by a conjugacy `e` is induced by `e⁻¹`. -/
@[simp]
theorem congr_symm (e : M ≃ₘ^n⟮I, J⟯ N) (h : Semiconj e φ ψ) :
    (congr e h).symm = congr e.symm (h.inverse_left e.symm_apply_apply e.apply_symm_apply) :=
  congrFamily_symm _ _ _ _

/-- The identity of `M` induces the identity of the mapping torus. -/
@[simp]
theorem congr_refl :
    congr (Diffeomorph.refl I M n) (Semiconj.id_left (ga := φ)) =
      Diffeomorph.refl (𝓘(ℝ).prod I) (SmoothMappingTorus φ) n :=
  congrFamily_refl

/-- The diffeomorphisms induced by conjugacies respect composition. -/
@[simp]
theorem congr_trans [T2Space P] [LocallyCompactSpace P] [IsManifold K n P]
    {χ : P ≃ₘ^n⟮K, K⟯ P} (e : M ≃ₘ^n⟮I, J⟯ N) (e' : N ≃ₘ^n⟮J, K⟯ P) (h : Semiconj e φ ψ)
    (h' : Semiconj e' ψ χ) :
    (congr e h).trans (congr e' h') = congr (e.trans e') (h'.comp_left h) :=
  congrFamily_trans _ _ _ _ _ _ _ _

end Congr

end SmoothMappingTorus

end TauCeti
