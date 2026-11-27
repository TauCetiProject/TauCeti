/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Delzant.Equiv
public import TauCeti.Geometry.Symplectic.Manifold.SymplecticMap
public import TauCeti.Geometry.Toric.Delzant.Quotient.Symplectic
public import TauCeti.Analysis.Normed.Lp.PiLp.Basic

/-!
# Naturality of the Delzant quotient

Let `i : N →+ V` be a lattice and `(u, c)` a facet presentation of a polytope
`Δ = {y ∈ V* | c j ≤ ⟨y, u j⟩ for every j}`, with Delzant quotient `M_Δ = Z / N_Δ`
(`TauCeti.Toric.DelzantQuotient i u c`), residual torus `(ℝ / 2πℤ)^ι / N_Δ` and reduced moment map
`μ_Δ : M_Δ → V*` (`TauCeti.Toric.DelzantQuotient.reducedMomentMap`). This file shows that `M_Δ`,
with its residual torus action and reduced moment map, is natural under relabelling the facets,
translating the polytope and changing the lattice.

* **Changes of presentation.** If a bijection `e : ι' ≃ ι` of facets carries the level and the
  kernel torus of one presentation to those of another, then `z ↦ z ∘ e.symm` descends to a
  homeomorphism of Delzant quotients (`TauCeti.Toric.DelzantQuotient.congr`), which intertwines
  the residual torus actions after relabelling the angles along `e`
  (`TauCeti.Toric.DelzantQuotient.congr_coe_vadd`).
* **Relabelling the facets.** Listing the facets along `e` gives the presentation
  `(u ∘ e, c ∘ e)` of the same polytope, and its Delzant quotient is identified with that of
  `(u, c)` (`TauCeti.Toric.DelzantQuotient.relabel`), preserving the reduced moment map.
* **Moment map shifts.** Translating the polytope by `y ∈ V*` adds `⟨y, u j⟩` to each support
  constant, and changes neither the level nor the kernel torus. The resulting identification of
  Delzant quotients commutes with the residual torus and shifts the reduced moment map by `y`
  (`TauCeti.Toric.DelzantQuotient.translate`,
  `TauCeti.Toric.DelzantQuotient.reducedMomentMap_translate`).
* **Changes of lattice.** A surjective lattice map `f : N → N'` and an injective linear map
  `g : V →L[ℝ] V'` with `g ∘ i = i' ∘ f`, for instance an integral linear change of coordinates,
  change neither the level nor the kernel torus of the mapped normals `f ∘ u`. The resulting
  identification of Delzant quotients carries the reduced moment map of `(f ∘ u, c)`, composed
  with `g`, to that of `(u, c)` (`TauCeti.Toric.DelzantQuotient.latticeCongr`,
  `TauCeti.Toric.DelzantQuotient.reducedMomentMap_latticeCongr_comp`). Together with moment map
  shifts, this is the behaviour of `M_Δ` under integral affine changes of `Δ`.

**Smooth and symplectic naturality.** For Delzant presentations in integral lattices, the Delzant
quotients are symplectic manifolds (`TauCeti.Toric.IsDelzant.delzantQuotientSymplecticForm`), and
all these identifications are equivariant symplectomorphisms. Relabelling the coordinates of
`ℂ^ι'` along `e` is a linear isometry on both factors of `ℂ^ι' = ℝ^ι' × ℝ^ι'`, so it preserves the
standard symplectic form `⟪x₁, y₂⟫ - ⟪y₁, x₂⟫`. Restricted to the levels it is a
diffeomorphism (`TauCeti.Toric.IsDelzant.delzantLevelCongrDiffeomorph`) preserving the restricted
forms. Since the projections from the levels are surjective submersions, it descends to a
diffeomorphism of Delzant quotients (`TauCeti.Toric.IsDelzant.delzantQuotientCongrDiffeomorph`),
which pulls the symplectic form back to the symplectic form, because the reduced forms are
characterized by their pullbacks to the levels
(`mpullback_delzantQuotientCongrDiffeomorph_delzantQuotientSymplecticForm`). In particular
relabelling the facets, shifting the moment map and changing the lattice are symplectomorphisms
(`TauCeti.Toric.IsDelzant.delzantQuotientRelabelDiffeomorph`,
`TauCeti.Toric.IsDelzant.delzantQuotientTranslateDiffeomorph`,
`TauCeti.Toric.IsDelzant.delzantQuotientLatticeCongrDiffeomorph`). Together with their effect on
the torus actions and the reduced moment maps above, this identifies the Hamiltonian torus
manifolds obtained from the presentations of a Delzant polytope related by these changes.

## Main definitions

* `TauCeti.Toric.DelzantQuotient.congr`: the homeomorphism of Delzant quotients induced by a
  bijection of facets along which the levels and kernel tori correspond.
* `TauCeti.Toric.DelzantQuotient.relabel`, `TauCeti.Toric.DelzantQuotient.translate`,
  `TauCeti.Toric.DelzantQuotient.latticeCongr`: the identifications of Delzant quotients under
  relabelling the facets, translating the polytope and changing the lattice.
* `TauCeti.Toric.IsDelzant.delzantLevelCongrDiffeomorph`,
  `TauCeti.Toric.IsDelzant.delzantQuotientCongrDiffeomorph`,
  `TauCeti.Toric.IsDelzant.delzantQuotientRelabelDiffeomorph`,
  `TauCeti.Toric.IsDelzant.delzantQuotientTranslateDiffeomorph`,
  `TauCeti.Toric.IsDelzant.delzantQuotientLatticeCongrDiffeomorph`: their smooth versions, for
  Delzant presentations in integral lattices.

## Main results

* `TauCeti.Toric.DelzantQuotient.congr_coe_vadd`, `TauCeti.Toric.DelzantQuotient.relabel_coe_vadd`,
  `TauCeti.Toric.DelzantQuotient.translate_vadd`,
  `TauCeti.Toric.DelzantQuotient.latticeCongr_coe_vadd`: these identifications intertwine the
  residual torus actions.
* `TauCeti.Toric.DelzantQuotient.reducedMomentMap_relabel`,
  `TauCeti.Toric.DelzantQuotient.reducedMomentMap_translate`,
  `TauCeti.Toric.DelzantQuotient.reducedMomentMap_latticeCongr_comp`: their effect on the reduced
  moment map.
* `TauCeti.Toric.IsDelzant.mpullback_delzantLevelCongrDiffeomorph_mpullback_coe_delzantLevel`:
  relabelling the coordinates of the levels preserves the restricted standard symplectic forms.
* `mpullback_delzantQuotientCongrDiffeomorph_delzantQuotientSymplecticForm`,
  `mpullback_delzantQuotientRelabelDiffeomorph_delzantQuotientSymplecticForm`,
  `mpullback_delzantQuotientTranslateDiffeomorph_delzantQuotientSymplecticForm` and
  `mpullback_delzantQuotientLatticeCongrDiffeomorph_delzantQuotientSymplecticForm`, in
  `TauCeti.Toric.IsDelzant`: these diffeomorphisms are symplectomorphisms for the symplectic forms
  of the Delzant quotients.
* `isSymplectomorphism_delzantQuotientCongrDiffeomorph` (with its inverse
  `isSymplectomorphism_delzantQuotientCongrDiffeomorph_symm`),
  `isSymplectomorphism_delzantQuotientRelabelDiffeomorph`,
  `isSymplectomorphism_delzantQuotientTranslateDiffeomorph` and
  `isSymplectomorphism_delzantQuotientLatticeCongrDiffeomorph`, in `TauCeti.Toric.IsDelzant`: the
  same statements with the predicate `TauCeti.SmoothTwoForm.IsSymplectomorphism`.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*,
  Bull. Soc. Math. France 116 (1988), 315–339.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 28–29.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 1.
-/

public section

noncomputable section

open Set Real Module Manifold
open scoped ContDiff

namespace TauCeti.Toric

variable {ι ι' N N' V V' : Type*} [Fintype ι] [Fintype ι'] [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {u : ι → N} {u' : ι' → N'} {c : ι → ℝ} {c' : ι' → ℝ}

namespace DelzantQuotient

/-! ### The general change of presentation -/

section Congr

variable (e : ι' ≃ ι)
  (hZ : ∀ x, Prod.map (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e)
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x ∈ delzantLevel i u c ↔ x ∈ delzantLevel i' u' c')
  (hN : ∀ θ : ι' → AddCircle (2 * π),
    θ ∘ e.symm ∈ (facetTorusHom i u (2 * π)).ker ↔ θ ∈ (facetTorusHom i' u' (2 * π)).ker)

include hN in
/-- **Changing the presentation of a Delzant quotient.** A bijection `e : ι' ≃ ι` of facets,
along which the levels and the kernel tori of two presentations correspond, induces a
homeomorphism of their Delzant quotients, sending the class of `z` to the class of `z ∘ e.symm`. -/
def congr : DelzantQuotient i' u' c' ≃ₜ DelzantQuotient i u c where
  toFun := lift (mk ∘ delzantLevelCongr e hZ) fun θ hθ x ↦ by
    simp only [Function.comp_apply, delzantLevelCongr_vadd, mk_vadd_of_mem_ker ((hN θ).2 hθ)]
  invFun := lift (mk ∘ (delzantLevelCongr e hZ).symm) fun θ hθ x ↦ by
    have hθ' : θ ∘ e ∈ (facetTorusHom i' u' (2 * π)).ker := (hN _).1 (by
      rwa [Function.comp_assoc, e.self_comp_symm, Function.comp_id])
    simp only [Function.comp_apply, delzantLevelCongr_symm_vadd, mk_vadd_of_mem_ker hθ']
  left_inv q := by
    induction q using DelzantQuotient.inductionOn with | h x => simp
  right_inv q := by
    induction q using DelzantQuotient.inductionOn with | h x => simp
  continuous_toFun := continuous_lift _ (continuous_mk.comp (delzantLevelCongr e hZ).continuous)
  continuous_invFun :=
    continuous_lift _ (continuous_mk.comp (delzantLevelCongr e hZ).symm.continuous)

@[simp]
theorem congr_mk (x : delzantLevel i' u' c') :
    congr e hZ hN (mk x) = mk (delzantLevelCongr e hZ x) :=
  lift_mk _ _ x

@[simp]
theorem congr_symm_mk (x : delzantLevel i u c) :
    (congr e hZ hN).symm (mk x) = mk ((delzantLevelCongr e hZ).symm x) :=
  lift_mk _ _ x

/-- The homeomorphism `congr` intertwines the residual torus actions, relabelling angles along
`e`. -/
@[simp]
theorem congr_coe_vadd (θ : ι' → AddCircle (2 * π)) (q : DelzantQuotient i' u' c') :
    congr e hZ hN ((θ : (ι' → AddCircle (2 * π)) ⧸ (facetTorusHom i' u' (2 * π)).ker) +ᵥ q) =
      ((θ ∘ e.symm : ι → AddCircle (2 * π)) :
        (ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker) +ᵥ congr e hZ hN q := by
  induction q using DelzantQuotient.inductionOn with | h x =>
  rw [coe_vadd_mk, congr_mk, congr_mk, delzantLevelCongr_vadd, coe_vadd_mk]

end Congr

/-! ### Relabelling the facets -/

section Relabel

variable (e : ι' ≃ ι)

/-- **Relabelling the facets.** Listing the facets of a presentation along a bijection
`e : ι' ≃ ι` gives a homeomorphic Delzant quotient, by the relabelling `z ↦ z ∘ e.symm` of the
coordinates of `ℂ^ι'`. -/
def relabel : DelzantQuotient i (u ∘ e) (c ∘ e) ≃ₜ DelzantQuotient i u c :=
  congr e (fun _ ↦ prodMap_piLpCongrLeft_mem_delzantLevel_iff e) fun θ ↦ by
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, facetTorusHom_comp_equiv]

@[simp]
theorem relabel_mk (x : delzantLevel i (u ∘ e) (c ∘ e)) :
    relabel e (mk x) = mk ⟨Prod.map (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e)
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x,
        (prodMap_piLpCongrLeft_mem_delzantLevel_iff e).2 x.property⟩ := by
  rw [relabel, congr_mk]
  exact congrArg mk (Subtype.ext (coe_delzantLevelCongr _ _ x))

@[simp]
theorem relabel_symm_mk (x : delzantLevel i u c) :
    (relabel e).symm (mk x) = mk ⟨Prod.map (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm)
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm) x,
        by rw [← coe_delzantLevelCongr_symm e
          fun _ ↦ prodMap_piLpCongrLeft_mem_delzantLevel_iff e]; exact Subtype.prop _⟩ := by
  rw [relabel, congr_symm_mk]
  exact congrArg mk (Subtype.ext (coe_delzantLevelCongr_symm e _ x))

/-- Relabelling the facets intertwines the residual torus actions, relabelling the angles. -/
@[simp]
theorem relabel_coe_vadd (θ : ι' → AddCircle (2 * π)) (q : DelzantQuotient i (u ∘ e) (c ∘ e)) :
    relabel e ((θ : (ι' → AddCircle (2 * π)) ⧸ (facetTorusHom i (u ∘ e) (2 * π)).ker) +ᵥ q) =
      ((θ ∘ e.symm : ι → AddCircle (2 * π)) :
        (ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker) +ᵥ relabel e q :=
  congr_coe_vadd _ _ _ θ q

/-- Relabelling the facets preserves the reduced moment map. -/
@[simp]
theorem reducedMomentMap_relabel [FiniteDimensional ℝ V]
    (hβ : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u j)))
    (hβ' : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u (e j))))
    (q : DelzantQuotient i (u ∘ e) (c ∘ e)) :
    reducedMomentMap hβ (relabel e q) = reducedMomentMap hβ' q := by
  induction q using DelzantQuotient.inductionOn with | h x =>
  rw [relabel_mk, reducedMomentMap_mk_eq_iff]
  intro j
  simpa [coe_delzantLevelCongr, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply] using (reducedMomentMap_mk_apply hβ' x (e.symm j)).symm

end Relabel

/-! ### Translating the polytope -/

section Translate

variable (y : StrongDual ℝ V)

/-- **Shifting the moment map.** Translating the polytope by `y ∈ V*`, that is adding `⟨y, u_j⟩`
to every support constant, does not change the level or the kernel torus, so it identifies the two
Delzant quotients. Under this identification the reduced moment map is shifted by `y`
(`TauCeti.Toric.DelzantQuotient.reducedMomentMap_translate`). -/
def translate : DelzantQuotient i u c ≃ₜ DelzantQuotient i u (fun j ↦ c j + y (i (u j))) :=
  congr (Equiv.refl ι)
    (fun _ ↦ by simp [delzantLevel_add]) fun _ ↦ by simp

@[simp]
theorem translate_mk (x : delzantLevel i u c) :
    translate y (mk x) = mk ⟨x, by rw [delzantLevel_add]; exact x.property⟩ := by
  rw [translate, congr_mk]
  exact congrArg mk (Subtype.ext (by simp))

@[simp]
theorem translate_symm_mk (x : delzantLevel i u (fun j ↦ c j + y (i (u j)))) :
    (translate y).symm (mk x) = mk ⟨x, by rw [← delzantLevel_add y]; exact x.property⟩ := by
  rw [translate, congr_symm_mk]
  exact congrArg mk (Subtype.ext (by simp))

/-- Translating the polytope commutes with the residual torus action. -/
@[simp]
theorem translate_vadd (θ : (ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker)
    (q : DelzantQuotient i u c) : translate y (θ +ᵥ q) = θ +ᵥ translate y q := by
  induction θ using QuotientAddGroup.induction_on with | H θ =>
  exact congr_coe_vadd _ _ _ θ q

/-- **Translating the polytope by `y` shifts the reduced moment map by `y`.** -/
@[simp]
theorem reducedMomentMap_translate [FiniteDimensional ℝ V]
    (hβ : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u j)))
    (q : DelzantQuotient i u c) :
    reducedMomentMap hβ (translate y q) = y + reducedMomentMap hβ q := by
  induction q using DelzantQuotient.inductionOn with | h x =>
  rw [translate_mk, reducedMomentMap_mk_eq_iff]
  intro j
  rw [add_apply, reducedMomentMap_mk_apply]
  ring

end Translate

/-! ### Lattice isomorphisms -/

section Lattice

variable {f : N → N'} {g : V →L[ℝ] V'} (hf : Function.Surjective f) (hg : Function.Injective g)
  (hfg : ∀ n, g (i n) = i' (f n))

include hf hg hfg in
/-- **Changing the lattice.** A surjective lattice map `f` and an injective real-linear map `g`
compatible with the lattice embeddings, `g ∘ i = i' ∘ f`, such as an integral linear change of
coordinates, do not change the level or the kernel torus, so they identify the Delzant quotient of
`(u, c)` with that of the mapped normals `(f ∘ u, c)`. Under this identification the reduced moment
maps correspond by the dual of `g`
(`TauCeti.Toric.DelzantQuotient.reducedMomentMap_latticeCongr_comp`). -/
def latticeCongr : DelzantQuotient i u c ≃ₜ DelzantQuotient i' (fun j ↦ f (u j)) c :=
  congr (Equiv.refl ι)
    (fun _ ↦ by simp [delzantLevel_comp_left hg hfg])
    fun _ ↦ by simp [ker_facetTorusHom_comp_left hf hg hfg]

@[simp]
theorem latticeCongr_mk (x : delzantLevel i u c) :
    latticeCongr hf hg hfg (mk x) = mk ⟨x, by rw [delzantLevel_comp_left hg hfg]; exact x.property⟩
        := by
  rw [latticeCongr, congr_mk]
  exact congrArg mk (Subtype.ext (by simp))

@[simp]
theorem latticeCongr_symm_mk (x : delzantLevel i' (fun j ↦ f (u j)) c) :
    (latticeCongr hf hg hfg).symm (mk x) =
      mk ⟨x, by rw [← delzantLevel_comp_left hg hfg]; exact x.property⟩ := by
  rw [latticeCongr, congr_symm_mk]
  exact congrArg mk (Subtype.ext (by simp))

/-- Changing the lattice commutes with the residual torus actions. -/
@[simp]
theorem latticeCongr_coe_vadd (θ : ι → AddCircle (2 * π)) (q : DelzantQuotient i u c) :
    latticeCongr hf hg hfg ((θ : (ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker) +ᵥ q) =
      (θ : (ι → AddCircle (2 * π)) ⧸ (facetTorusHom i' (fun j ↦ f (u j)) (2 * π)).ker) +ᵥ
        latticeCongr hf hg hfg q :=
  congr_coe_vadd _ _ _ θ q

/-- **Changing the lattice transforms the reduced moment map by the dual map**: the reduced moment
map of the mapped normals, composed with `g`, is the reduced moment map of `(u, c)`. -/
@[simp]
theorem reducedMomentMap_latticeCongr_comp [FiniteDimensional ℝ V] [FiniteDimensional ℝ V']
    (hβ : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u j)))
    (hβ' : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i' (f (u j))))
    (q : DelzantQuotient i u c) :
    (reducedMomentMap hβ' (latticeCongr hf hg hfg q)).comp g = reducedMomentMap hβ q := by
  induction q using DelzantQuotient.inductionOn with | h x =>
  rw [eq_comm, reducedMomentMap_mk_eq_iff]
  intro j
  simp [hfg, reducedMomentMap_mk_apply]

end Lattice

end DelzantQuotient

/-! ### Smooth structures and symplectic forms -/

namespace IsDelzant

variable [FiniteDimensional ℝ V] [FiniteDimensional ℝ V'] (hΔ : IsDelzant i u c)
  (hΔ' : IsDelzant i' u' c') (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')

section Congr

variable (e : ι' ≃ ι)
  (hZ : ∀ x, Prod.map (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e)
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x ∈ delzantLevel i u c ↔ x ∈ delzantLevel i' u' c')
  (hN : ∀ θ : ι' → AddCircle (2 * π),
    θ ∘ e.symm ∈ (facetTorusHom i u (2 * π)).ker ↔ θ ∈ (facetTorusHom i' u' (2 * π)).ker)

include hZ in
/-- **Relabelling the coordinates of the level is a diffeomorphism.** For Delzant presentations in
integral lattices whose levels correspond along `e : ι' ≃ ι`, the relabelling
`TauCeti.Toric.delzantLevelCongr` of coordinates is a smooth diffeomorphism of the levels, for
their implicit-function atlases `TauCeti.Toric.IsDelzant.delzantLevelChartedSpace`. -/
def delzantLevelCongrDiffeomorph :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := hΔ'.delzantLevelChartedSpace hi'
    delzantLevel i' u' c' ≃ₘ⟮𝓘(ℝ, Fin (Fintype.card ι' + finrank ℝ V') → ℝ),
      𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)⟯ delzantLevel i u c :=
  letI := hΔ.delzantLevelChartedSpace hi
  letI := hΔ'.delzantLevelChartedSpace hi'
  -- Both maps are restrictions of the linear relabelling of coordinates and of its inverse.
  { toEquiv := (delzantLevelCongr e hZ).toEquiv
    contMDiff_toFun := by
      convert hΔ.contMDiff_codRestrict_delzantLevel hi
        (((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).contDiff.prodMap
          (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).contDiff).contMDiff.comp
            (hΔ'.contMDiff_coe_delzantLevel hi' (m := ∞)))
        (fun x ↦ (hZ x).2 x.property) using 1
      exact funext fun x ↦ Subtype.ext (coe_delzantLevelCongr e hZ x)
    contMDiff_invFun := by
      convert hΔ'.contMDiff_codRestrict_delzantLevel hi'
        (((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm).contDiff.prodMap
          (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm).contDiff).contMDiff.comp
            (hΔ.contMDiff_coe_delzantLevel hi (m := ∞)))
        (fun x ↦ by
          rw [Function.comp_apply, ← coe_delzantLevelCongr_symm e hZ]
          exact Subtype.prop _) using 1
      exact funext fun x ↦ Subtype.ext (coe_delzantLevelCongr_symm e hZ x) }

@[simp]
theorem coe_delzantLevelCongrDiffeomorph :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := hΔ'.delzantLevelChartedSpace hi'
    ⇑(hΔ.delzantLevelCongrDiffeomorph hΔ' hi hi' e hZ) = delzantLevelCongr e hZ :=
  (rfl)

@[simp]
theorem coe_delzantLevelCongrDiffeomorph_symm :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := hΔ'.delzantLevelChartedSpace hi'
    ⇑(hΔ.delzantLevelCongrDiffeomorph hΔ' hi hi' e hZ).symm = (delzantLevelCongr e hZ).symm :=
  (rfl)

include hN in
/-- **Changing the presentation of a Delzant quotient is a diffeomorphism.** For Delzant
presentations in integral lattices whose levels and kernel tori correspond along `e : ι' ≃ ι`, the
homeomorphism `TauCeti.Toric.DelzantQuotient.congr` of Delzant quotients is a smooth
diffeomorphism, for the quotient manifold atlases
`TauCeti.Toric.IsDelzant.delzantQuotientChartedSpace`. -/
def delzantQuotientCongrDiffeomorph :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := hΔ'.delzantQuotientChartedSpace hi'
    DelzantQuotient i' u' c' ≃ₘ⟮
      𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i' u')
        (Fin (Fintype.card ι' + finrank ℝ V') → ℝ)),
      𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ))⟯ DelzantQuotient i u c :=
  letI := hΔ.delzantLevelChartedSpace hi
  letI := hΔ'.delzantLevelChartedSpace hi'
  letI := hΔ.delzantQuotientChartedSpace hi
  letI := hΔ'.delzantQuotientChartedSpace hi'
  haveI := hΔ.isManifold_delzantLevel hi ∞
  haveI := hΔ'.isManifold_delzantLevel hi' ∞
  haveI := hΔ.isManifold_delzantQuotient hi
  haveI := hΔ'.isManifold_delzantQuotient hi'
  -- Both maps are smooth after composing with the projections from the levels, which are
  -- surjective submersions: the composites are the projections composed with the relabelling of
  -- the levels and with its inverse.
  { toEquiv := (DelzantQuotient.congr e hZ hN).toEquiv
    contMDiff_toFun := by
      refine ((hΔ'.isSubmersion_delzantQuotientMk hi').contMDiff_comp_iff
        DelzantQuotient.mk_surjective le_rfl).1 ?_
      convert (hΔ.isSubmersion_delzantQuotientMk hi).contMDiff.comp
        (hΔ.delzantLevelCongrDiffeomorph hΔ' hi hi' e hZ).contMDiff using 1
      exact funext fun x ↦ DelzantQuotient.congr_mk e hZ hN x
    contMDiff_invFun := by
      refine ((hΔ.isSubmersion_delzantQuotientMk hi).contMDiff_comp_iff
        DelzantQuotient.mk_surjective le_rfl).1 ?_
      convert (hΔ'.isSubmersion_delzantQuotientMk hi').contMDiff.comp
        (hΔ.delzantLevelCongrDiffeomorph hΔ' hi hi' e hZ).symm.contMDiff using 1
      exact funext fun x ↦ DelzantQuotient.congr_symm_mk e hZ hN x }

@[simp]
theorem coe_delzantQuotientCongrDiffeomorph :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := hΔ'.delzantQuotientChartedSpace hi'
    ⇑(hΔ.delzantQuotientCongrDiffeomorph hΔ' hi hi' e hZ hN) = DelzantQuotient.congr e hZ hN :=
  (rfl)

@[simp]
theorem coe_delzantQuotientCongrDiffeomorph_symm :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := hΔ'.delzantQuotientChartedSpace hi'
    ⇑(hΔ.delzantQuotientCongrDiffeomorph hΔ' hi hi' e hZ hN).symm =
      (DelzantQuotient.congr e hZ hN).symm :=
  (rfl)

/-- **Relabelling the coordinates preserves the restricted symplectic form.** The diffeomorphism
`delzantLevelCongrDiffeomorph` of levels pulls the restriction of the standard symplectic form of
`ℂ^ι` back to the restriction of the standard symplectic form of `ℂ^ι'`: relabelling coordinates
along `e` is a linear isometry applied to both factors of `ℂ^ι' = ℝ^ι' × ℝ^ι'`. -/
theorem mpullback_delzantLevelCongrDiffeomorph_mpullback_coe_delzantLevel :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := hΔ'.delzantLevelChartedSpace hi'
    haveI := hΔ.isManifold_delzantLevel hi ∞
    haveI := hΔ'.isManifold_delzantLevel hi' ∞
    SmoothForm.mpullback (hΔ.delzantLevelCongrDiffeomorph hΔ' hi hi' e hZ)
        (hΔ.delzantLevelCongrDiffeomorph hΔ' hi hi' e hZ).contMDiff
        (SmoothForm.mpullback ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
          (hΔ.contMDiff_coe_delzantLevel hi) stdSymplecticForm.constSmooth) =
      SmoothForm.mpullback
        ((↑) : delzantLevel i' u' c' → EuclideanSpace ℝ ι' × EuclideanSpace ℝ ι')
        (hΔ'.contMDiff_coe_delzantLevel hi') stdSymplecticForm.constSmooth := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := hΔ'.delzantLevelChartedSpace hi'
  have := hΔ.isManifold_delzantLevel hi ∞
  have := hΔ'.isManifold_delzantLevel hi' ∞
  -- Read in `ℂ^ι' → ℂ^ι`, the relabelling of the levels is the linear equivalence `L`, which
  -- preserves the standard symplectic forms.
  let L : (EuclideanSpace ℝ ι' × EuclideanSpace ℝ ι') ≃L[ℝ]
      EuclideanSpace ℝ ι × EuclideanSpace ℝ ι :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).toContinuousLinearEquiv.prodCongr
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).toContinuousLinearEquiv
  have hL : SymplecticForm.IsSymplectomorphism stdSymplecticForm stdSymplecticForm
      (L : (EuclideanSpace ℝ ι' × EuclideanSpace ℝ ι') ≃ₗ[ℝ]
        EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :=
    SymplecticForm.isSymplectomorphism_iff.2 fun v w ↦ by
      simp [L, LinearIsometryEquiv.inner_map_map]
  rw [SmoothForm.mpullback_mpullback_of_comp_eq
      (hΔ.delzantLevelCongrDiffeomorph hΔ' hi hi' e hZ).contMDiff
      (hΔ.contMDiff_coe_delzantLevel hi) (hΔ'.contMDiff_coe_delzantLevel hi')
      L.toDiffeomorph.contMDiff (funext fun x ↦ coe_delzantLevelCongr e hZ x),
    SymplecticForm.IsSymplectomorphism.mpullback_constSmooth hL]

/-- **Changing the presentation of a Delzant quotient is a symplectomorphism.** The
diffeomorphism `delzantQuotientCongrDiffeomorph` pulls the symplectic form `ω_Δ` of the Delzant
quotient of `(u, c)` back to the symplectic form of the Delzant quotient of `(u', c')`. -/
theorem mpullback_delzantQuotientCongrDiffeomorph_delzantQuotientSymplecticForm :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := hΔ'.delzantQuotientChartedSpace hi'
    haveI := hΔ.isManifold_delzantQuotient hi
    haveI := hΔ'.isManifold_delzantQuotient hi'
    SmoothForm.mpullback (hΔ.delzantQuotientCongrDiffeomorph hΔ' hi hi' e hZ hN)
        (hΔ.delzantQuotientCongrDiffeomorph hΔ' hi hi' e hZ hN).contMDiff
        (hΔ.delzantQuotientSymplecticForm hi) =
      hΔ'.delzantQuotientSymplecticForm hi' := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := hΔ'.delzantLevelChartedSpace hi'
  let _ := hΔ.delzantQuotientChartedSpace hi
  let _ := hΔ'.delzantQuotientChartedSpace hi'
  have := hΔ.isManifold_delzantLevel hi ∞
  have := hΔ'.isManifold_delzantLevel hi' ∞
  have := hΔ.isManifold_delzantQuotient hi
  have := hΔ'.isManifold_delzantQuotient hi'
  -- Both forms are determined by their pullbacks to the level of `(u', c')`, where the projection
  -- followed by the change of presentation is the relabelling of the levels followed by the
  -- projection.
  rw [hΔ'.eq_delzantQuotientSymplecticForm_iff hi',
    SmoothForm.mpullback_mpullback_of_comp_eq (hΔ'.isSubmersion_delzantQuotientMk hi').contMDiff
      (hΔ.delzantQuotientCongrDiffeomorph hΔ' hi hi' e hZ hN).contMDiff
      (hΔ.delzantLevelCongrDiffeomorph hΔ' hi hi' e hZ).contMDiff
      (hΔ.isSubmersion_delzantQuotientMk hi).contMDiff
      (funext fun x ↦ DelzantQuotient.congr_mk e hZ hN x),
    hΔ.mpullback_delzantQuotientMk_delzantQuotientSymplecticForm hi,
    hΔ.mpullback_delzantLevelCongrDiffeomorph_mpullback_coe_delzantLevel hΔ' hi hi' e hZ]

/-- **Changing the presentation of a Delzant quotient is a symplectomorphism**, stated with the
predicate `TauCeti.SmoothTwoForm.IsSymplectomorphism`: `delzantQuotientCongrDiffeomorph` is a
symplectomorphism from the symplectic form of the Delzant quotient of `(u', c')` to that of
`(u, c)`. -/
theorem isSymplectomorphism_delzantQuotientCongrDiffeomorph :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := hΔ'.delzantQuotientChartedSpace hi'
    haveI := hΔ.isManifold_delzantQuotient hi
    haveI := hΔ'.isManifold_delzantQuotient hi'
    SmoothTwoForm.IsSymplectomorphism (hΔ'.delzantQuotientSymplecticForm hi')
      (hΔ.delzantQuotientSymplecticForm hi)
      (hΔ.delzantQuotientCongrDiffeomorph hΔ' hi hi' e hZ hN) :=
  letI := hΔ.delzantQuotientChartedSpace hi
  letI := hΔ'.delzantQuotientChartedSpace hi'
  haveI := hΔ.isManifold_delzantQuotient hi
  haveI := hΔ'.isManifold_delzantQuotient hi'
  SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq.2
    (hΔ.mpullback_delzantQuotientCongrDiffeomorph_delzantQuotientSymplecticForm hΔ' hi hi' e hZ hN)

/-- The inverse of `delzantQuotientCongrDiffeomorph` is a symplectomorphism from the symplectic
form of the Delzant quotient of `(u, c)` to that of `(u', c')`. -/
theorem isSymplectomorphism_delzantQuotientCongrDiffeomorph_symm :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := hΔ'.delzantQuotientChartedSpace hi'
    haveI := hΔ.isManifold_delzantQuotient hi
    haveI := hΔ'.isManifold_delzantQuotient hi'
    SmoothTwoForm.IsSymplectomorphism (hΔ.delzantQuotientSymplecticForm hi)
      (hΔ'.delzantQuotientSymplecticForm hi')
      (hΔ.delzantQuotientCongrDiffeomorph hΔ' hi hi' e hZ hN).symm :=
  letI := hΔ.delzantQuotientChartedSpace hi
  letI := hΔ'.delzantQuotientChartedSpace hi'
  haveI := hΔ.isManifold_delzantQuotient hi
  haveI := hΔ'.isManifold_delzantQuotient hi'
  (hΔ.isSymplectomorphism_delzantQuotientCongrDiffeomorph hΔ' hi hi' e hZ hN).symm (by simp)

end Congr

/-! #### Relabelling, translation and changes of lattice -/

section Relabel

variable (e : ι' ≃ ι)

/-- **Relabelling the facets is a symplectomorphism of Delzant quotients.** For a Delzant
presentation in an integral lattice and a bijection `e : ι' ≃ ι`, the homeomorphism
`TauCeti.Toric.DelzantQuotient.relabel` from the Delzant quotient of the relabelled presentation
`(u ∘ e, c ∘ e)` is a smooth diffeomorphism. It pulls the symplectic form back to the symplectic
form (`mpullback_delzantQuotientRelabelDiffeomorph_delzantQuotientSymplecticForm`, in
`TauCeti.Toric.IsDelzant`) and preserves the reduced moment map
(`TauCeti.Toric.DelzantQuotient.reducedMomentMap_relabel`). -/
def delzantQuotientRelabelDiffeomorph :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := (hΔ.comp_equiv e).delzantQuotientChartedSpace hi
    DelzantQuotient i (u ∘ e) (c ∘ e) ≃ₘ⟮
      𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i (u ∘ e))
        (Fin (Fintype.card ι' + finrank ℝ V) → ℝ)),
      𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ))⟯ DelzantQuotient i u c :=
  hΔ.delzantQuotientCongrDiffeomorph (hΔ.comp_equiv e) hi hi e
    (fun _ ↦ prodMap_piLpCongrLeft_mem_delzantLevel_iff e) fun θ ↦ by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, facetTorusHom_comp_equiv]

@[simp]
theorem coe_delzantQuotientRelabelDiffeomorph :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := (hΔ.comp_equiv e).delzantQuotientChartedSpace hi
    ⇑(hΔ.delzantQuotientRelabelDiffeomorph hi e) = DelzantQuotient.relabel e :=
  (rfl)

@[simp]
theorem coe_delzantQuotientRelabelDiffeomorph_symm :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := (hΔ.comp_equiv e).delzantQuotientChartedSpace hi
    ⇑(hΔ.delzantQuotientRelabelDiffeomorph hi e).symm = (DelzantQuotient.relabel e).symm :=
  (rfl)

/-- Relabelling the facets pulls the symplectic form of the Delzant quotient back to the symplectic
form of the Delzant quotient of the relabelled presentation. -/
theorem mpullback_delzantQuotientRelabelDiffeomorph_delzantQuotientSymplecticForm :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := (hΔ.comp_equiv e).delzantQuotientChartedSpace hi
    haveI := hΔ.isManifold_delzantQuotient hi
    haveI := (hΔ.comp_equiv e).isManifold_delzantQuotient hi
    SmoothForm.mpullback (hΔ.delzantQuotientRelabelDiffeomorph hi e)
        (hΔ.delzantQuotientRelabelDiffeomorph hi e).contMDiff
        (hΔ.delzantQuotientSymplecticForm hi) =
      (hΔ.comp_equiv e).delzantQuotientSymplecticForm hi :=
  hΔ.mpullback_delzantQuotientCongrDiffeomorph_delzantQuotientSymplecticForm _ hi hi e _ _

/-- Relabelling the facets is a symplectomorphism from the symplectic form of the Delzant quotient
of the relabelled presentation to the symplectic form of the Delzant quotient of `(u, c)`. -/
theorem isSymplectomorphism_delzantQuotientRelabelDiffeomorph :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := (hΔ.comp_equiv e).delzantQuotientChartedSpace hi
    haveI := hΔ.isManifold_delzantQuotient hi
    haveI := (hΔ.comp_equiv e).isManifold_delzantQuotient hi
    SmoothTwoForm.IsSymplectomorphism ((hΔ.comp_equiv e).delzantQuotientSymplecticForm hi)
      (hΔ.delzantQuotientSymplecticForm hi) (hΔ.delzantQuotientRelabelDiffeomorph hi e) :=
  hΔ.isSymplectomorphism_delzantQuotientCongrDiffeomorph _ hi hi e _ _

end Relabel

section Translate

variable (y : StrongDual ℝ V)

/-- **Shifting the moment map is a symplectomorphism of Delzant quotients.** For a Delzant
presentation in an integral lattice and `y ∈ V*`, the identification
`TauCeti.Toric.DelzantQuotient.translate` of the Delzant quotient of `(u, c)` with that of the
polytope translated by `y` is a smooth diffeomorphism. It pulls the symplectic form back to the
symplectic form (`mpullback_delzantQuotientTranslateDiffeomorph_delzantQuotientSymplecticForm`, in
`TauCeti.Toric.IsDelzant`), commutes with the torus action
(`TauCeti.Toric.DelzantQuotient.translate_vadd`) and shifts the
reduced moment map by `y` (`TauCeti.Toric.DelzantQuotient.reducedMomentMap_translate`). -/
def delzantQuotientTranslateDiffeomorph :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := ((isDelzant_add_iff y).2 hΔ).delzantQuotientChartedSpace hi
    DelzantQuotient i u c ≃ₘ⟮
      𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ)),
      𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ))⟯
      DelzantQuotient i u (fun j ↦ c j + y (i (u j))) :=
  ((isDelzant_add_iff y).2 hΔ).delzantQuotientCongrDiffeomorph hΔ hi hi (Equiv.refl ι)
    (fun _ ↦ by simp [delzantLevel_add]) fun _ ↦ by simp

@[simp]
theorem coe_delzantQuotientTranslateDiffeomorph :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := ((isDelzant_add_iff y).2 hΔ).delzantQuotientChartedSpace hi
    ⇑(hΔ.delzantQuotientTranslateDiffeomorph hi y) = DelzantQuotient.translate y :=
  (rfl)

@[simp]
theorem coe_delzantQuotientTranslateDiffeomorph_symm :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := ((isDelzant_add_iff y).2 hΔ).delzantQuotientChartedSpace hi
    ⇑(hΔ.delzantQuotientTranslateDiffeomorph hi y).symm = (DelzantQuotient.translate y).symm :=
  (rfl)

/-- Shifting the moment map pulls the symplectic form of the Delzant quotient of the translated
polytope back to the symplectic form of the Delzant quotient of `(u, c)`. -/
theorem mpullback_delzantQuotientTranslateDiffeomorph_delzantQuotientSymplecticForm :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := ((isDelzant_add_iff y).2 hΔ).delzantQuotientChartedSpace hi
    haveI := hΔ.isManifold_delzantQuotient hi
    haveI := ((isDelzant_add_iff y).2 hΔ).isManifold_delzantQuotient hi
    SmoothForm.mpullback (hΔ.delzantQuotientTranslateDiffeomorph hi y)
        (hΔ.delzantQuotientTranslateDiffeomorph hi y).contMDiff
        (((isDelzant_add_iff y).2 hΔ).delzantQuotientSymplecticForm hi) =
      hΔ.delzantQuotientSymplecticForm hi :=
  mpullback_delzantQuotientCongrDiffeomorph_delzantQuotientSymplecticForm
    ((isDelzant_add_iff y).2 hΔ) hΔ hi hi _ _ _

/-- Shifting the moment map is a symplectomorphism from the symplectic form of the Delzant
quotient of `(u, c)` to the symplectic form of the Delzant quotient of the translated polytope. -/
theorem isSymplectomorphism_delzantQuotientTranslateDiffeomorph :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := ((isDelzant_add_iff y).2 hΔ).delzantQuotientChartedSpace hi
    haveI := hΔ.isManifold_delzantQuotient hi
    haveI := ((isDelzant_add_iff y).2 hΔ).isManifold_delzantQuotient hi
    SmoothTwoForm.IsSymplectomorphism (hΔ.delzantQuotientSymplecticForm hi)
      (((isDelzant_add_iff y).2 hΔ).delzantQuotientSymplecticForm hi)
      (hΔ.delzantQuotientTranslateDiffeomorph hi y) :=
  isSymplectomorphism_delzantQuotientCongrDiffeomorph ((isDelzant_add_iff y).2 hΔ) hΔ hi hi _ _ _

end Translate

section Lattice

variable {f : N → N'} {g : V →L[ℝ] V'} (hf : Function.Surjective f) (hg : Function.Injective g)
  (hfg : ∀ n, g (i n) = i' (f n)) (hΔf : IsDelzant i' (fun j ↦ f (u j)) c)

include hf hg hfg in
/-- **Changing the lattice is a symplectomorphism of Delzant quotients.** For a surjective lattice
map `f` and an injective real-linear map `g` with `g ∘ i = i' ∘ f`, and Delzant presentations
`(u, c)` and `(f ∘ u, c)` in integral lattices, the identification
`TauCeti.Toric.DelzantQuotient.latticeCongr` of their Delzant quotients is a smooth diffeomorphism.
It pulls the symplectic form back to the symplectic form
(`mpullback_delzantQuotientLatticeCongrDiffeomorph_delzantQuotientSymplecticForm`, in
`TauCeti.Toric.IsDelzant`), commutes with the torus action
(`TauCeti.Toric.DelzantQuotient.latticeCongr_coe_vadd`) and transforms the reduced moment map by
the dual of `g` (`TauCeti.Toric.DelzantQuotient.reducedMomentMap_latticeCongr_comp`). -/
def delzantQuotientLatticeCongrDiffeomorph :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := hΔf.delzantQuotientChartedSpace hi'
    DelzantQuotient i u c ≃ₘ⟮
      𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ)),
      𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i' fun j ↦ f (u j))
        (Fin (Fintype.card ι + finrank ℝ V') → ℝ))⟯
      DelzantQuotient i' (fun j ↦ f (u j)) c :=
  hΔf.delzantQuotientCongrDiffeomorph hΔ hi' hi (Equiv.refl ι)
    (fun _ ↦ by simp [delzantLevel_comp_left hg hfg])
    fun _ ↦ by simp [ker_facetTorusHom_comp_left hf hg hfg]

@[simp]
theorem coe_delzantQuotientLatticeCongrDiffeomorph :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := hΔf.delzantQuotientChartedSpace hi'
    ⇑(hΔ.delzantQuotientLatticeCongrDiffeomorph hi hi' hf hg hfg hΔf) =
      DelzantQuotient.latticeCongr hf hg hfg :=
  (rfl)

@[simp]
theorem coe_delzantQuotientLatticeCongrDiffeomorph_symm :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := hΔf.delzantQuotientChartedSpace hi'
    ⇑(hΔ.delzantQuotientLatticeCongrDiffeomorph hi hi' hf hg hfg hΔf).symm =
      (DelzantQuotient.latticeCongr hf hg hfg).symm :=
  (rfl)

/-- Changing the lattice pulls the symplectic form of the Delzant quotient of `(f ∘ u, c)` back to
the symplectic form of the Delzant quotient of `(u, c)`. -/
theorem mpullback_delzantQuotientLatticeCongrDiffeomorph_delzantQuotientSymplecticForm :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := hΔf.delzantQuotientChartedSpace hi'
    haveI := hΔ.isManifold_delzantQuotient hi
    haveI := hΔf.isManifold_delzantQuotient hi'
    SmoothForm.mpullback (hΔ.delzantQuotientLatticeCongrDiffeomorph hi hi' hf hg hfg hΔf)
        (hΔ.delzantQuotientLatticeCongrDiffeomorph hi hi' hf hg hfg hΔf).contMDiff
        (hΔf.delzantQuotientSymplecticForm hi') =
      hΔ.delzantQuotientSymplecticForm hi :=
  hΔf.mpullback_delzantQuotientCongrDiffeomorph_delzantQuotientSymplecticForm hΔ hi' hi _ _ _

/-- Changing the lattice is a symplectomorphism from the symplectic form of the Delzant quotient of
`(u, c)` to the symplectic form of the Delzant quotient of `(f ∘ u, c)`. -/
theorem isSymplectomorphism_delzantQuotientLatticeCongrDiffeomorph :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := hΔf.delzantQuotientChartedSpace hi'
    haveI := hΔ.isManifold_delzantQuotient hi
    haveI := hΔf.isManifold_delzantQuotient hi'
    SmoothTwoForm.IsSymplectomorphism (hΔ.delzantQuotientSymplecticForm hi)
      (hΔf.delzantQuotientSymplecticForm hi')
      (hΔ.delzantQuotientLatticeCongrDiffeomorph hi hi' hf hg hfg hΔf) :=
  hΔf.isSymplectomorphism_delzantQuotientCongrDiffeomorph hΔ hi' hi _ _ _

end Lattice

end IsDelzant

end TauCeti.Toric
