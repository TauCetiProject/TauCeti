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
`Y_φ` and `Y_ψ` (`TauCeti.SmoothMappingTorus`). A map `g : M → N` intertwining them,
`g ∘ φ = ψ ∘ g`, induces the map

`[t, x] ↦ [t, g x]`

of mapping tori (`TauCeti.SmoothMappingTorus.map φ ψ g h`). It lies over the circle and
intertwines the two suspension flows, and it is `C^n` when `g` is. Maps of mapping tori are
functorial in `g`.

A diffeomorphism `e : M ≃ₘ^n⟮I, J⟯ N` with `e ∘ φ = ψ ∘ e`, a *conjugacy* from `φ` to `ψ`,
induces a diffeomorphism `Y_φ ≃ Y_ψ` (`TauCeti.SmoothMappingTorus.congr e h`). For example
`e` conjugates `φ` to `e ∘ φ ∘ e⁻¹`, so conjugate diffeomorphisms have diffeomorphic mapping tori,
by a diffeomorphism over the circle that intertwines the suspension flows and sends the fibre
inclusion `x ↦ [t, x]` to `y ↦ [t, y]` after `e`.

The induced maps agree with those of Tau Ceti's topological mapping torus `TauCeti.MappingTorus`
under the homeomorphisms `TauCeti.SmoothMappingTorus.homeomorphMappingTorus`.

## Main definitions

* `TauCeti.SmoothMappingTorus.map φ ψ g h`: the map `[t, x] ↦ [t, g x]` of mapping tori induced by
  a map `g` intertwining `φ` and `ψ`.
* `TauCeti.SmoothMappingTorus.congr e h`: the diffeomorphism of mapping tori induced by a
  diffeomorphism `e` conjugating `φ` to `ψ`.

## Main results

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

/-! ### The induced map -/

section Map

variable (φ : M ≃ₘ^n⟮I, I⟯ M) (ψ : N ≃ₘ^n⟮J, J⟯ N) (g : M → N) (h : Semiconj g φ ψ)

/-- The map `[t, x] ↦ [t, g x]` of mapping tori induced by a map `g` intertwining the
diffeomorphisms `φ` and `ψ`, `g ∘ φ = ψ ∘ g`. It is well defined because `g` also intertwines all
integer powers of `φ` and `ψ`. -/
def map : SmoothMappingTorus φ → SmoothMappingTorus ψ :=
  MulAction.orbitRelQuotientLift (fun z ↦ mk ψ ((ofProd φ).symm z).1 (g ((ofProd φ).symm z).2))
    fun k z ↦ by
      rw [ofProd_symm_smul, mk_add_intCast, ← h.diffeomorph_zpow_right, zpow_neg]
      simp

/-- The induced map sends `[t, x]` to `[t, g x]`. -/
@[simp]
theorem map_mk (t : ℝ) (x : M) : map φ ψ g h (mk φ t x) = mk ψ t (g x) := by
  rw [map, mk_def φ, MulAction.orbitRelQuotientLift_mk, Equiv.symm_apply_apply]

/-- On `ℝ × M`, the induced map is `(t, x) ↦ (t, g x)` followed by the quotient map of `Y_ψ`. -/
theorem map_comp_uncurry_mk :
    map φ ψ g h ∘ uncurry (mk φ) = uncurry (mk ψ) ∘ Prod.map id g :=
  funext fun p ↦ map_mk φ ψ g h p.1 p.2

/-- The induced map lies over the circle. -/
@[simp]
theorem proj_map (z : SmoothMappingTorus φ) : proj ψ (map φ ψ g h z) = proj φ z := by
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
  simp

/-- The induced map lies over the circle, as an equality of functions. -/
theorem proj_comp_map : proj ψ ∘ map φ ψ g h = proj φ :=
  funext (proj_map φ ψ g h)

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
  continuous_orbitRelQuotientLift_iff.2 <| (continuous_uncurry_mk ψ).comp
    ((continuous_ofProd_symm φ).fst.prodMk (hg.comp (continuous_ofProd_symm φ).snd))

/-- The identity of `M` induces the identity of the mapping torus. -/
@[simp]
theorem map_id : map φ φ id (Semiconj.id_left) = id := by
  funext z
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
  simp

/-- Maps of mapping tori respect composition of maps intertwining the monodromies. -/
@[simp]
theorem map_map (χ : P ≃ₘ^n⟮K, K⟯ P) (g' : N → P) (h' : Semiconj g' ψ χ)
    (z : SmoothMappingTorus φ) :
    map ψ χ g' h' (map φ ψ g h z) = map φ χ (g' ∘ g) (h'.comp_left h) z := by
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
  simp

/-- The induced map is the map of topological mapping tori induced by `g`, under the
homeomorphisms `TauCeti.SmoothMappingTorus.homeomorphMappingTorus`. -/
theorem homeomorphMappingTorus_map (hg : Continuous g) (z : SmoothMappingTorus φ) :
    homeomorphMappingTorus ψ (map φ ψ g h z) =
      MappingTorus.map φ.toHomeomorph.symm ψ.toHomeomorph.symm ⟨g, hg⟩
        (Semiconj.inverses_right h φ.toEquiv.right_inv ψ.toEquiv.left_inv)
        (homeomorphMappingTorus φ z) := by
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
  simp

section Manifold

variable [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] [T2Space N]
  [LocallyCompactSpace N] [IsManifold J n N]

/-- The induced map is `C^n` when `g` is. -/
theorem contMDiff_map (hg : ContMDiff I J n g) :
    ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod J) n (map φ ψ g h) := by
  rw [← (isLocalDiffeomorph_uncurry_mk φ).contMDiff_comp_iff (uncurry_mk_surjective φ) le_rfl,
    map_comp_uncurry_mk]
  exact (contMDiff_uncurry_mk ψ).comp (contMDiff_fst.prodMk (hg.comp contMDiff_snd))

end Manifold

end Map

/-! ### Conjugacies -/

section Congr

variable [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] [T2Space N]
  [LocallyCompactSpace N] [IsManifold J n N]
  {φ : M ≃ₘ^n⟮I, I⟯ M} {ψ : N ≃ₘ^n⟮J, J⟯ N}

/-- The diffeomorphism `[t, x] ↦ [t, e x]` of mapping tori induced by a diffeomorphism `e`
conjugating `φ` to `ψ`, `e ∘ φ = ψ ∘ e`. Its inverse is induced by `e⁻¹`
(`TauCeti.SmoothMappingTorus.congr_symm`). -/
def congr (e : M ≃ₘ^n⟮I, J⟯ N) (h : Semiconj e φ ψ) :
    SmoothMappingTorus φ ≃ₘ^n⟮𝓘(ℝ).prod I, 𝓘(ℝ).prod J⟯ SmoothMappingTorus ψ where
  toFun := map φ ψ e h
  invFun := map ψ φ e.symm (h.inverse_left e.symm_apply_apply e.apply_symm_apply)
  left_inv z := by
    obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
    simp
  right_inv z := by
    obtain ⟨⟨t, y⟩, rfl⟩ := uncurry_mk_surjective ψ z
    simp
  contMDiff_toFun := contMDiff_map φ ψ e h e.contMDiff
  contMDiff_invFun :=
    contMDiff_map ψ φ e.symm (h.inverse_left e.symm_apply_apply e.apply_symm_apply) e.symm.contMDiff

/-- The diffeomorphism induced by a conjugacy `e` is the map induced by `e`. -/
@[simp]
theorem coe_congr (e : M ≃ₘ^n⟮I, J⟯ N) (h : Semiconj e φ ψ) :
    ⇑(congr e h) = map φ ψ e h :=
  (rfl)

/-- The inverse of the diffeomorphism induced by a conjugacy `e` is induced by `e⁻¹`. -/
@[simp]
theorem congr_symm (e : M ≃ₘ^n⟮I, J⟯ N) (h : Semiconj e φ ψ) :
    (congr e h).symm = congr e.symm (h.inverse_left e.symm_apply_apply e.apply_symm_apply) :=
  (rfl)

/-- The identity of `M` induces the identity of the mapping torus. -/
@[simp]
theorem congr_refl :
    congr (Diffeomorph.refl I M n) (Semiconj.id_left (ga := φ)) =
      Diffeomorph.refl (𝓘(ℝ).prod I) (SmoothMappingTorus φ) n :=
  Diffeomorph.ext fun z ↦ congrFun (map_id φ) z

/-- The diffeomorphisms induced by conjugacies respect composition. -/
@[simp]
theorem congr_trans [T2Space P] [LocallyCompactSpace P] [IsManifold K n P]
    {χ : P ≃ₘ^n⟮K, K⟯ P} (e : M ≃ₘ^n⟮I, J⟯ N) (e' : N ≃ₘ^n⟮J, K⟯ P) (h : Semiconj e φ ψ)
    (h' : Semiconj e' ψ χ) :
    (congr e h).trans (congr e' h') = congr (e.trans e') (h'.comp_left h) :=
  Diffeomorph.ext fun z ↦ map_map φ ψ e h χ e' h' z

end Congr

end SmoothMappingTorus

end TauCeti
