/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Delzant.Quotient.Basic
public import TauCeti.Analysis.Normed.Lp.PiLp

/-!
# Naturality of the Delzant quotient and its orbit space

Let `i : N →+ V` be a lattice and `(u, c)` a facet presentation of a polytope
`Δ = {y ∈ V* | c j ≤ ⟨y, u j⟩ for every j}`, with Delzant quotient `M_Δ = Z / N_Δ`
(`TauCeti.Toric.DelzantQuotient i u c`), residual torus `(ℝ / 2πℤ)^ι / N_Δ` and reduced moment map
`μ_Δ : M_Δ → V*` (`TauCeti.Toric.DelzantQuotient.reducedMomentMap`). This file shows that `M_Δ`,
with its residual torus action and reduced moment map, is natural under relabelling the facets,
translating the polytope and changing the lattice, and that `μ_Δ` identifies the orbit space of
the residual torus with `Δ`.

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
* **The orbit space.** When the real normals span `V` and `Δ` is bounded, as for a Delzant
  polytope, `μ_Δ` is invariant under the residual torus, has image `Δ`, and its fibres are the
  orbits. As `M_Δ` is compact, `μ_Δ` therefore induces a homeomorphism from the orbit space of
  the residual torus onto `Δ` (`TauCeti.Toric.DelzantQuotient.orbitRelQuotientHomeomorph`).

## Main definitions

* `TauCeti.Toric.DelzantQuotient.congr`: the homeomorphism of Delzant quotients induced by a
  bijection of facets along which the levels and kernel tori correspond.
* `TauCeti.Toric.DelzantQuotient.relabel`, `TauCeti.Toric.DelzantQuotient.translate`,
  `TauCeti.Toric.DelzantQuotient.latticeCongr`: the identifications of Delzant quotients under
  relabelling the facets, translating the polytope and changing the lattice.
* `TauCeti.Toric.DelzantQuotient.orbitRelQuotientHomeomorph`: the homeomorphism from the orbit
  space of the residual torus onto `Δ`.

## Main results

* `TauCeti.Toric.DelzantQuotient.congr_coe_vadd`, `TauCeti.Toric.DelzantQuotient.relabel_coe_vadd`,
  `TauCeti.Toric.DelzantQuotient.translate_vadd`,
  `TauCeti.Toric.DelzantQuotient.latticeCongr_coe_vadd`: these identifications intertwine the
  residual torus actions.
* `TauCeti.Toric.DelzantQuotient.reducedMomentMap_relabel`,
  `TauCeti.Toric.DelzantQuotient.reducedMomentMap_translate`,
  `TauCeti.Toric.DelzantQuotient.reducedMomentMap_latticeCongr_comp`: their effect on the reduced
  moment map.
* `TauCeti.Toric.DelzantQuotient.coe_orbitRelQuotientHomeomorph_mk`: the orbit space
  homeomorphism sends the orbit of `q` to `μ_Δ(q)`.

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

open Set Real

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
        (prodMap_piLpCongrLeft_mem_delzantLevel_iff e).2 x.2⟩ := by
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
    translate y (mk x) = mk ⟨x, by rw [delzantLevel_add]; exact x.2⟩ := by
  rw [translate, congr_mk]
  exact congrArg mk (Subtype.ext (by simp))

@[simp]
theorem translate_symm_mk (x : delzantLevel i u (fun j ↦ c j + y (i (u j)))) :
    (translate y).symm (mk x) = mk ⟨x, by rw [← delzantLevel_add y]; exact x.2⟩ := by
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
    latticeCongr hf hg hfg (mk x) = mk ⟨x, by rw [delzantLevel_comp_left hg hfg]; exact x.2⟩ := by
  rw [latticeCongr, congr_mk]
  exact congrArg mk (Subtype.ext (by simp))

@[simp]
theorem latticeCongr_symm_mk (x : delzantLevel i' (fun j ↦ f (u j)) c) :
    (latticeCongr hf hg hfg).symm (mk x) =
      mk ⟨x, by rw [← delzantLevel_comp_left hg hfg]; exact x.2⟩ := by
  rw [latticeCongr, congr_symm_mk]
  exact congrArg mk (Subtype.ext (by simp))

/-- Changing the lattice commutes with the residual torus actions. -/
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

/-! ### The orbit space of the residual torus -/

section OrbitSpace

variable [FiniteDimensional ℝ V]
  (hβ : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u j)))

/-- **The orbit space of a Delzant quotient is its polytope.** When the real normals span `V` and
the polytope `Δ` is bounded, as for a Delzant polytope, the reduced moment map induces a
homeomorphism from the orbit space of the residual torus action on `M_Δ` onto `Δ`. -/
def orbitRelQuotientHomeomorph (hb : Bornology.IsBounded (facetPolyhedron i u c)) :
    AddAction.orbitRel.Quotient ((ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker)
      (DelzantQuotient i u c) ≃ₜ facetPolyhedron i u c :=
  haveI := compactSpace_delzantQuotient hb
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective
    (Quotient.lift
      (fun q ↦ ⟨reducedMomentMap hβ q, reducedMomentMap_mem_facetPolyhedron hβ q⟩)
      fun q q' h ↦ by
        obtain ⟨θ, rfl⟩ := AddAction.orbitRel_apply.1 h
        exact Subtype.ext (reducedMomentMap_vadd hβ θ q'))
    ⟨fun a b h ↦ by
      induction a using Quotient.inductionOn with | h q =>
      induction b using Quotient.inductionOn with | h q' =>
      obtain ⟨θ, hθ⟩ := (reducedMomentMap_eq_reducedMomentMap_iff hβ).1 (congrArg Subtype.val h)
      exact Quotient.sound ⟨θ, hθ⟩,
    fun ⟨y, hy⟩ ↦ by
      rw [← range_reducedMomentMap hβ] at hy
      obtain ⟨q, rfl⟩ := hy
      exact ⟨Quotient.mk _ q, rfl⟩⟩)
    (continuous_quot_lift _ ((continuous_reducedMomentMap hβ).subtype_mk _))

/-- The homeomorphism `orbitRelQuotientHomeomorph` sends the orbit of `q` to `μ_Δ(q)`. -/
@[simp]
theorem coe_orbitRelQuotientHomeomorph_mk (hb : Bornology.IsBounded (facetPolyhedron i u c))
    (q : DelzantQuotient i u c) :
    (orbitRelQuotientHomeomorph hβ hb (Quotient.mk _ q) : StrongDual ℝ V) =
      reducedMomentMap hβ q :=
  (rfl)

end OrbitSpace

end DelzantQuotient

end TauCeti.Toric
