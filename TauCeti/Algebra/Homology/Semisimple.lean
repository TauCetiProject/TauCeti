/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Complexes of semisimple modules are homotopy equivalent to complexes with zero differential

Let `K` be a homological complex of modules over a ring `R`, of any shape, whose terms are
semisimple modules; for instance any complex of vector spaces over a division ring, or of modules
over a semisimple ring.  Then `K` is chain homotopy equivalent to a complex with zero
differentials (`HomologicalComplex.exists_homotopyEquiv_d_eq_zero`).  Since a homotopy
equivalence induces isomorphisms on homology (`HomotopyEquiv.toHomologyIso`) and the homology of
a complex with zero differentials is its terms, the terms of that complex are the homology of
`K`: over a division ring every complex is homotopy equivalent to its homology.

The construction is the classical splitting.  In each degree `i` write `Zᵢ` for the cycles, the
kernel of the differential out of `i`, and `Bᵢ ≤ Zᵢ` for the boundaries, the range of the
differential into `i`.  Choose a complement `Cᵢ` of `Zᵢ` in `Kᵢ` and a complement `Hᵢ` of `Bᵢ`
in `Zᵢ`, so that `Kᵢ = Bᵢ ⊕ Hᵢ ⊕ Cᵢ`.  For a relation `j → i` of the shape the differential
restricts to an isomorphism `Cⱼ ≃ Bᵢ`.  The complex with terms `Hᵢ` and zero differentials then
includes into `K` and is retracted from it by the projection along `Bᵢ ⊕ Cᵢ`; the composite on
`K` differs from the identity by `d h + h d`, where `h : Kᵢ ⟶ Kⱼ` is the projection onto `Bᵢ`
followed by the inverse of `Cⱼ ≃ Bᵢ`.

The result reduces statements about the homology of complexes of vector spaces, such as the
Künneth theorem over a field, to complexes with zero differential.

## Main results

* `HomologicalComplex.exists_homotopyEquiv_d_eq_zero`: a complex of semisimple modules is
  homotopy equivalent to a complex with zero differentials.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 1.4 (split complexes).
-/

public section

noncomputable section

open CategoryTheory

universe v u

namespace HomologicalComplex

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{v} R) c)

namespace SemisimpleSplitting

/-! ### Cycles, boundaries and the chosen complements -/

/-- The cycles of `K` in degree `i`: the kernel of the differential out of `i`. -/
private def cyc (i : ι) : Submodule R (K.X i) :=
  LinearMap.ker (K.d i (c.next i)).hom

/-- The boundaries of `K` in degree `i`: the range of the differential into `i`. -/
private def bdry (i : ι) : Submodule R (K.X i) :=
  LinearMap.range (K.d (c.prev i) i).hom

private lemma cyc_eq {i j : ι} (r : c.Rel i j) : cyc K i = LinearMap.ker (K.d i j).hom := by
  rw [cyc, c.next_eq' r]

private lemma bdry_eq {i j : ι} (r : c.Rel j i) : bdry K i = LinearMap.range (K.d j i).hom := by
  rw [bdry, c.prev_eq' r]

private lemma d_apply_eq_zero {i : ι} {x : K.X i} (hx : x ∈ cyc K i) (j : ι) :
    (K.d i j).hom x = 0 := by
  by_cases r : c.Rel i j
  · rwa [cyc_eq K r] at hx
  · simp [K.shape i j r]

private lemma d_apply_mem_bdry (i j : ι) (x : K.X j) : (K.d j i).hom x ∈ bdry K i := by
  by_cases r : c.Rel j i
  · rw [bdry_eq K r]
    exact ⟨x, rfl⟩
  · simp [K.shape j i r]

private lemma bdry_le_cyc (i : ι) : bdry K i ≤ cyc K i := by
  rintro _ ⟨x, rfl⟩
  rw [cyc, LinearMap.mem_ker, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, K.d_comp_d,
    ModuleCat.hom_zero, LinearMap.zero_apply]

private lemma d_apply_mem_cyc (i j : ι) (x : K.X j) : (K.d j i).hom x ∈ cyc K i :=
  bdry_le_cyc K i (d_apply_mem_bdry K i j x)

private lemma cyc_eq_top {i : ι} (h : ∀ l, ¬c.Rel i l) : cyc K i = ⊤ := by
  simp [cyc, K.shape i (c.next i) (h _)]

private lemma bdry_eq_bot {i : ι} (h : ∀ l, ¬c.Rel l i) : bdry K i = ⊥ := by
  simp [bdry, K.shape (c.prev i) i (h _)]

variable [∀ i, IsSemisimpleModule R (K.X i)]

/-- A complement of the cycles in degree `i`. -/
private def compl (i : ι) : Submodule R (K.X i) :=
  (exists_isCompl (cyc K i)).choose

private lemma isCompl_cyc_compl (i : ι) : IsCompl (cyc K i) (compl K i) :=
  (exists_isCompl (cyc K i)).choose_spec

/-- The boundaries in degree `i`, as a submodule of the cycles. -/
private def bdryCyc (i : ι) : Submodule R (cyc K i) :=
  (bdry K i).comap (cyc K i).subtype

/-- A complement of the boundaries in the cycles in degree `i`; it maps isomorphically onto the
homology in degree `i`. -/
private def harm (i : ι) : Submodule R (cyc K i) :=
  (exists_isCompl (bdryCyc K i)).choose

private lemma isCompl_bdryCyc_harm (i : ι) : IsCompl (bdryCyc K i) (harm K i) :=
  (exists_isCompl (bdryCyc K i)).choose_spec

/-! ### The projections of the decomposition `Kᵢ = Bᵢ ⊕ Hᵢ ⊕ Cᵢ` -/

/-- The projection of `Kᵢ` onto the cycles along the chosen complement. -/
private def toCyc (i : ι) : K.X i →ₗ[R] cyc K i :=
  (cyc K i).projectionOnto (compl K i) (isCompl_cyc_compl K i)

/-- The projection of `Kᵢ` onto the chosen complement of the cycles. -/
private def toCompl (i : ι) : K.X i →ₗ[R] compl K i :=
  (compl K i).projectionOnto (cyc K i) (isCompl_cyc_compl K i).symm

/-- The projection of `Kᵢ` onto the boundaries. -/
private def toBdry (i : ι) : K.X i →ₗ[R] bdryCyc K i :=
  (bdryCyc K i).projectionOnto (harm K i) (isCompl_bdryCyc_harm K i) ∘ₗ toCyc K i

/-- The projection of `Kᵢ` onto the chosen complement of the boundaries in the cycles. -/
private def toHarm (i : ι) : K.X i →ₗ[R] harm K i :=
  (harm K i).projectionOnto (bdryCyc K i) (isCompl_bdryCyc_harm K i).symm ∘ₗ toCyc K i

/-- The inclusion of the chosen complement of the boundaries in the cycles into `Kᵢ`. -/
private def ofHarm (i : ι) : harm K i →ₗ[R] K.X i :=
  (cyc K i).subtype ∘ₗ (harm K i).subtype

omit [∀ i, IsSemisimpleModule R (K.X i)] in
private lemma mem_bdryCyc {i : ι} {x : K.X i} (hx : x ∈ bdry K i) :
    (⟨x, bdry_le_cyc K i hx⟩ : cyc K i) ∈ bdryCyc K i :=
  hx

private lemma toCyc_apply_of_mem {i : ι} {x : K.X i} (hx : x ∈ cyc K i) :
    toCyc K i x = ⟨x, hx⟩ :=
  Submodule.projectionOnto_apply_of_mem_left _ hx

private lemma toBdry_apply_of_mem {i : ι} {x : K.X i} (hx : x ∈ bdry K i) :
    toBdry K i x = ⟨⟨x, bdry_le_cyc K i hx⟩, hx⟩ := by
  rw [toBdry, LinearMap.comp_apply, toCyc_apply_of_mem K (bdry_le_cyc K i hx)]
  exact Submodule.projectionOnto_apply_of_mem_left _ (mem_bdryCyc K hx)

private lemma toHarm_apply_of_mem {i : ι} {x : K.X i} (hx : x ∈ bdry K i) :
    toHarm K i x = 0 := by
  rw [toHarm, LinearMap.comp_apply, toCyc_apply_of_mem K (bdry_le_cyc K i hx)]
  exact Submodule.projectionOnto_apply_of_mem_right _ (mem_bdryCyc K hx)

private lemma toHarm_ofHarm (i : ι) (x : harm K i) : toHarm K i (ofHarm K i x) = x := by
  rw [toHarm, LinearMap.comp_apply, ofHarm, LinearMap.comp_apply, Submodule.subtype_apply,
    Submodule.subtype_apply, toCyc_apply_of_mem K (x : cyc K i).2]
  exact Submodule.projectionOnto_apply_left _ x

private lemma ofHarm_apply_mem (i : ι) (x : harm K i) : ofHarm K i x ∈ cyc K i :=
  (x : cyc K i).2

private lemma coe_toCyc_add_coe_toCompl (i : ι) (x : K.X i) :
    (toCyc K i x : K.X i) + (toCompl K i x : K.X i) = x :=
  Submodule.projection_add_projection_eq_self (isCompl_cyc_compl K i) x

/-- Every element of `Kᵢ` is the sum of its components in `Cᵢ`, `Bᵢ` and `Hᵢ`. -/
private lemma toCompl_add_toBdry_add_ofHarm_toHarm (i : ι) (x : K.X i) :
    (toCompl K i x : K.X i) + ((toBdry K i x : cyc K i) : K.X i) + ofHarm K i (toHarm K i x) =
      x := by
  have hZ : (toBdry K i x : cyc K i) + (toHarm K i x : cyc K i) = toCyc K i x :=
    Submodule.projection_add_projection_eq_self (isCompl_bdryCyc_harm K i) (toCyc K i x)
  rw [add_assoc, ofHarm, LinearMap.comp_apply, Submodule.subtype_apply, Submodule.subtype_apply,
    ← Submodule.coe_add, hZ, add_comm, coe_toCyc_add_coe_toCompl]

private lemma toCompl_eq_zero {i : ι} (h : ∀ l, ¬c.Rel i l) (x : K.X i) : toCompl K i x = 0 :=
  Submodule.projectionOnto_apply_of_mem_right _ (by simp [cyc_eq_top K h])

private lemma toBdry_eq_zero {i : ι} (h : ∀ l, ¬c.Rel l i) (x : K.X i) :
    ((toBdry K i x : cyc K i) : K.X i) = 0 := by
  have : ((toBdry K i x : cyc K i) : K.X i) ∈ bdry K i := (toBdry K i x).2
  rwa [bdry_eq_bot K h, Submodule.mem_bot] at this

/-! ### The differential identifies `Cⱼ` with `Bᵢ` -/

/-- The differential `Kⱼ ⟶ Kᵢ` restricted to the chosen complement `Cⱼ` of the cycles, with
values in the boundaries `Bᵢ`. -/
private def dCompl (i j : ι) : compl K j →ₗ[R] bdryCyc K i :=
  LinearMap.codRestrict (bdryCyc K i)
    (LinearMap.codRestrict (cyc K i) ((K.d j i).hom ∘ₗ (compl K j).subtype)
      fun x ↦ d_apply_mem_cyc K i j x)
    fun x ↦ d_apply_mem_bdry K i j x

private lemma coe_dCompl (i j : ι) (x : compl K j) :
    ((dCompl K i j x : cyc K i) : K.X i) = (K.d j i).hom x :=
  rfl

private lemma d_apply_toCompl (i j : ι) (x : K.X j) :
    (K.d j i).hom (toCompl K j x) = (K.d j i).hom x := by
  conv_rhs => rw [← coe_toCyc_add_coe_toCompl K j x]
  rw [map_add, d_apply_eq_zero K (toCyc K j x).2, zero_add]

private lemma dCompl_bijective {i j : ι} (r : c.Rel j i) : Function.Bijective (dCompl K i j) := by
  refine ⟨?_, fun y ↦ ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have hx' : (x : K.X j) ∈ cyc K j := by
      rw [cyc_eq K r, LinearMap.mem_ker, ← coe_dCompl K i j, hx, Submodule.coe_zero,
        Submodule.coe_zero]
    exact Subtype.ext ((Submodule.disjoint_def.1 (isCompl_cyc_compl K j).disjoint) _ hx' x.2)
  · obtain ⟨x, hx⟩ : ((y : cyc K i) : K.X i) ∈ LinearMap.range (K.d j i).hom := by
      rw [← bdry_eq K r]
      exact y.2
    refine ⟨toCompl K j x, Subtype.ext (Subtype.ext ?_)⟩
    rw [coe_dCompl, d_apply_toCompl K i j]
    exact hx

/-- For a relation `j → i` of the shape, the isomorphism `Cⱼ ≃ Bᵢ` given by the differential. -/
private def dComplEquiv {i j : ι} (r : c.Rel j i) : compl K j ≃ₗ[R] bdryCyc K i :=
  LinearEquiv.ofBijective (dCompl K i j) (dCompl_bijective K r)

private lemma coe_dComplEquiv {i j : ι} (r : c.Rel j i) (x : compl K j) :
    ((dComplEquiv K r x : cyc K i) : K.X i) = (K.d j i).hom x :=
  rfl

/-! ### The contracting homotopy -/

/-- The homotopy `Kᵢ ⟶ Kⱼ` for a relation `j → i` of the shape: the projection onto `Bᵢ`
followed by the inverse of `Cⱼ ≃ Bᵢ`. -/
private def htpy (i j : ι) (r : c.Rel j i) : K.X i ⟶ K.X j :=
  ModuleCat.ofHom ((compl K j).subtype ∘ₗ (dComplEquiv K r).symm.toLinearMap ∘ₗ toBdry K i)

private lemma htpy_apply {i j : ι} (r : c.Rel j i) (x : K.X i) :
    (htpy K i j r).hom x = (dComplEquiv K r).symm (toBdry K i x) :=
  rfl

/-- `d ∘ h` is the projection onto the boundaries. -/
private lemma d_htpy_apply {i j : ι} (r : c.Rel j i) (x : K.X i) :
    (K.d j i).hom ((htpy K i j r).hom x) = ((toBdry K i x : cyc K i) : K.X i) := by
  rw [htpy_apply, ← coe_dComplEquiv K r, LinearEquiv.apply_symm_apply]

/-- `h ∘ d` is the projection onto the chosen complement of the cycles. -/
private lemma htpy_d_apply {i j : ι} (r : c.Rel i j) (x : K.X i) :
    (htpy K j i r).hom ((K.d i j).hom x) = toCompl K i x := by
  have : dComplEquiv K r (toCompl K i x) = toBdry K j (K.d i j x) := by
    rw [toBdry_apply_of_mem K (d_apply_mem_bdry K j i x)]
    exact Subtype.ext (Subtype.ext (d_apply_toCompl K j i x))
  rw [htpy_apply, ← this, LinearEquiv.symm_apply_apply]

/-! ### The complex with zero differentials -/

/-- The complex with the chosen complements `Hᵢ` of the boundaries in the cycles as terms and
zero differentials. -/
private def harmComplex : HomologicalComplex (ModuleCat.{v} R) c where
  X i := ModuleCat.of R (harm K i)
  d _ _ := 0

/-- The inclusion of `Hᵢ` into `Kᵢ`, a chain map since `Hᵢ` consists of cycles. -/
private def incl : harmComplex K ⟶ K where
  f i := ModuleCat.ofHom (ofHarm K i)
  comm' i j _ := by
    ext x
    -- both sides unfold to elements of `Kⱼ`; the differential of the source complex is `0`
    exact (d_apply_eq_zero K (ofHarm_apply_mem K i x) j).trans (map_zero (ofHarm K j)).symm

/-- The projection of `Kᵢ` onto `Hᵢ` along `Bᵢ ⊕ Cᵢ`, a chain map since it kills boundaries. -/
private def proj : K ⟶ harmComplex K where
  f i := ModuleCat.ofHom (toHarm K i)
  comm' i j _ := by
    ext x
    -- both sides unfold to elements of `Hⱼ`; the differential of the target complex is `0`
    exact (toHarm_apply_of_mem K (d_apply_mem_bdry K j i x)).symm

private lemma incl_f_hom (i : ι) : ((incl K).f i).hom = ofHarm K i :=
  rfl

private lemma proj_f_hom (i : ι) : ((proj K).f i).hom = toHarm K i :=
  rfl

private lemma incl_proj : incl K ≫ proj K = 𝟙 _ := by
  ext i x
  exact toHarm_ofHarm K i x

/-- The identity of `K` minus the idempotent `incl ∘ proj` is `d h + h d`.  In each degree this
is the decomposition of an element into its components in `Cᵢ`, `Bᵢ` and `Hᵢ`: `h d` recovers
the `Cᵢ`-component and `d h` the `Bᵢ`-component; there is no `Cᵢ`-component when no differential
leaves `i`, and no `Bᵢ`-component when none arrives. -/
private lemma id_sub_proj_incl :
    𝟙 K - proj K ≫ incl K = Homotopy.nullHomotopicMap' (htpy K) := by
  ext i x
  have hdec := toCompl_add_toBdry_add_ofHarm_toHarm K i x
  simp only [sub_f_apply, id_f, comp_f, ModuleCat.hom_sub, ModuleCat.hom_id, ModuleCat.hom_comp,
    LinearMap.sub_apply, LinearMap.id_apply, incl_f_hom, proj_f_hom]
  by_cases hn : c.Rel i (c.next i) <;> by_cases hp : c.Rel (c.prev i) i
  · rw [Homotopy.nullHomotopicMap'_f hp hn]
    simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply]
    rw [htpy_d_apply, d_htpy_apply]
    exact (eq_sub_of_add_eq hdec).symm
  · have hp' : ∀ l, ¬c.Rel l i := fun l hl ↦ hp (by rwa [c.prev_eq' hl])
    rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right hn hp']
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [htpy_d_apply]
    rw [toBdry_eq_zero K hp', add_zero] at hdec
    exact (eq_sub_of_add_eq hdec).symm
  · have hn' : ∀ l, ¬c.Rel i l := fun l hl ↦ hn (by rwa [c.next_eq' hl])
    rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left hp hn']
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [d_htpy_apply]
    rw [toCompl_eq_zero K hn', Submodule.coe_zero, zero_add] at hdec
    exact (eq_sub_of_add_eq hdec).symm
  · have hp' : ∀ l, ¬c.Rel l i := fun l hl ↦ hp (by rwa [c.prev_eq' hl])
    have hn' : ∀ l, ¬c.Rel i l := fun l hl ↦ hn (by rwa [c.next_eq' hl])
    rw [Homotopy.nullHomotopicMap'_f_eq_zero hn' hp', ModuleCat.hom_zero, LinearMap.zero_apply,
      sub_eq_zero]
    rw [toCompl_eq_zero K hn', toBdry_eq_zero K hp', Submodule.coe_zero, zero_add,
      zero_add] at hdec
    exact hdec.symm

/-- The homotopy equivalence between `K` and the complex with terms `Hᵢ` and zero
differentials. -/
private def homotopyEquiv : HomotopyEquiv K (harmComplex K) where
  hom := proj K
  inv := incl K
  homotopyHomInvId :=
    (Homotopy.equivSubZero.symm
      ((Homotopy.ofEq (id_sub_proj_incl K)).trans (Homotopy.nullHomotopy' (htpy K)))).symm
  homotopyInvHomId := Homotopy.ofEq (incl_proj K)

end SemisimpleSplitting

variable [∀ i, IsSemisimpleModule R (K.X i)]

open SemisimpleSplitting in
/-- A complex of semisimple modules, for instance a complex of vector spaces over a division ring,
is chain homotopy equivalent to a complex with zero differentials.  The terms of such a complex
are its homology, so by `HomotopyEquiv.toHomologyIso` they are the homology of `K`. -/
theorem exists_homotopyEquiv_d_eq_zero :
    ∃ L : HomologicalComplex (ModuleCat.{v} R) c, (∀ i j, L.d i j = 0) ∧
      Nonempty (HomotopyEquiv K L) :=
  ⟨harmComplex K, fun _ _ ↦ rfl, ⟨homotopyEquiv K⟩⟩

end HomologicalComplex
