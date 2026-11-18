/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SquareZero.Quotient

/-!
# Filtered chain homotopy equivalences

Let `d` and `e` be linear endomorphisms of modules `M` and `N`, filtered by families of submodules
`F i` of `M` and `G i` of `N` indexed by a type `ι`. A **filtered chain homotopy equivalence**
(`LinearMap.FilteredHomotopyEquiv d e F G`) consists of chain maps `f : M → N` and `g : N → M`,
`f ∘ d = e ∘ f` and `g ∘ e = d ∘ g`, together with chain homotopies

`g ∘ f - 1 = d ∘ h + h ∘ d`, `f ∘ g - 1 = e ∘ k + k ∘ e`,

all four of `f`, `g`, `h` and `k` preserving the filtrations: `f (F i) ⊆ G i`, `g (G i) ⊆ F i`,
`h (F i) ⊆ F i` and `k (G i) ⊆ G i` for every `i`. Knot Floer homology is the filtered chain
homotopy type of a filtered complex, the knot filtration of a Heegaard Floer complex or the
Alexander filtration of a grid complex, and its invariance is proved by exhibiting filtered chain
homotopy equivalences under the elementary moves.

Filtered chain homotopy equivalences form an equivalence relation: there is an identity
(`LinearMap.FilteredHomotopyEquiv.refl`), an inverse (`LinearMap.FilteredHomotopyEquiv.symm`) and
a composite (`LinearMap.FilteredHomotopyEquiv.trans`). A linear equivalence intertwining the
differentials and carrying each level of one filtration onto the corresponding level of the other
is one, with zero homotopies (`LinearMap.FilteredHomotopyEquiv.ofLinearEquiv`).

Because every map preserves the filtrations, a filtered chain homotopy equivalence restricts to
each level `F j` of the filtration (`LinearMap.FilteredHomotopyEquiv.restrict`) and descends to
each quotient `M ⧸ F j` (`LinearMap.FilteredHomotopyEquiv.quotient`), as soon as `d` preserves
`F j` and `e` preserves `G j`; both are again filtered chain homotopy equivalences, for the induced
filtrations. When `d` and `e` square to zero, a filtered chain homotopy equivalence induces an
isomorphism of homologies (`LinearMap.FilteredHomotopyEquiv.homologyEquiv`), since homotopic chain
maps induce the same map on homology (`LinearMap.homologyMap_eq_of_sub_eq`). Restricting to `F j`
and then dividing by the trace `F i ∩ F j` gives isomorphisms between the homologies of all the
subquotients `F j ⧸ (F i ∩ F j)` and `G j ⧸ (G i ∩ G j)`, that is, `F j ⧸ F i` and `G j ⧸ G i`
when `F i ≤ F j` and `G i ≤ G j` (`LinearMap.FilteredHomotopyEquiv.subquotientHomologyEquiv`). For a
filtration indexed by `ℤ` the subquotients `F a ⧸ F (a - 1)` form the associated graded complex,
so the homology of the associated graded complex (the first page of the spectral sequence of the
filtration) is an invariant of the filtered chain homotopy type.

The filtrations are arbitrary families of submodules: they need not be increasing, exhaustive or
separated, and the index type `ι` need not be ordered. This covers the filtrations by several
Alexander gradings of links, indexed by `ℤⁿ`. The differentials need not square to zero except
where homology is taken. The structure records the four maps elementwise, as linear maps, rather
than as a homotopy equivalence of complexes in a category of modules, so that the restrictions to
the levels and the induced maps on the quotients can be formed.

## Main definitions

* `LinearMap.FilteredHomotopyEquiv d e F G`: a filtered chain homotopy equivalence.
* `LinearMap.FilteredHomotopyEquiv.refl`, `LinearMap.FilteredHomotopyEquiv.symm`,
  `LinearMap.FilteredHomotopyEquiv.trans`: the identity, the inverse and the composite.
* `LinearMap.FilteredHomotopyEquiv.ofLinearEquiv`: the filtered chain homotopy equivalence of a
  filtered isomorphism of complexes.
* `LinearMap.FilteredHomotopyEquiv.restrict`: the restriction to a level of the filtrations.
* `LinearMap.FilteredHomotopyEquiv.quotient`: the quotient by a level of the filtrations.
* `LinearMap.FilteredHomotopyEquiv.homologyEquiv`: the induced isomorphism of homologies.
* `LinearMap.FilteredHomotopyEquiv.subquotientHomologyEquiv`: the induced isomorphisms of the
  homologies of the subquotients `F j ⧸ (F i ∩ F j)` and `G j ⧸ (G i ∩ G j)`.

## Main results

* `LinearMap.FilteredHomotopyEquiv.homologyEquiv_refl`,
  `LinearMap.FilteredHomotopyEquiv.homologyEquiv_symm`,
  `LinearMap.FilteredHomotopyEquiv.homologyEquiv_trans`: the isomorphisms of homologies are
  functorial.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Appendix A (filtered chain complexes, filtered chain homotopy
  equivalences and their associated graded complexes) and Chapter 13 (the filtered grid complex).
* P. Ozsváth, Z. Szabó, *Holomorphic disks and knot invariants*, Adv. Math. 186 (2004),
  [arXiv:math/0209056](https://arxiv.org/abs/math/0209056) (the knot filtration and the invariance
  of its filtered chain homotopy type).
-/

public section

namespace LinearMap

variable {S M N P : Type*} [Ring S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
  [AddCommGroup P] [Module S P] {ι : Type*}

/-- A **filtered chain homotopy equivalence** between the linear endomorphisms `d` of `M` and `e`
of `N`, filtered by the families of submodules `F` of `M` and `G` of `N`: chain maps `hom` and
`inv` with chain homotopies `inv ∘ hom - 1 = d ∘ h + h ∘ d` and
`hom ∘ inv - 1 = e ∘ k + k ∘ e`, all four maps preserving every level of the filtrations. -/
@[ext]
structure FilteredHomotopyEquiv (d : M →ₗ[S] M) (e : N →ₗ[S] N) (F : ι → Submodule S M)
    (G : ι → Submodule S N) where
  /-- The chain map from `M` to `N`. -/
  hom : M →ₗ[S] N
  /-- The chain map from `N` to `M`. -/
  inv : N →ₗ[S] M
  /-- The chain homotopy from `inv ∘ hom` to the identity of `M`. -/
  homotopyHomInvId : M →ₗ[S] M
  /-- The chain homotopy from `hom ∘ inv` to the identity of `N`. -/
  homotopyInvHomId : N →ₗ[S] N
  hom_comm : hom ∘ₗ d = e ∘ₗ hom
  inv_comm : inv ∘ₗ e = d ∘ₗ inv
  homotopyHomInvId_comm :
    inv ∘ₗ hom - LinearMap.id = d ∘ₗ homotopyHomInvId + homotopyHomInvId ∘ₗ d
  homotopyInvHomId_comm :
    hom ∘ₗ inv - LinearMap.id = e ∘ₗ homotopyInvHomId + homotopyInvHomId ∘ₗ e
  le_comap_hom (i : ι) : F i ≤ (G i).comap hom
  le_comap_inv (i : ι) : G i ≤ (F i).comap inv
  le_comap_homotopyHomInvId (i : ι) : F i ≤ (F i).comap homotopyHomInvId
  le_comap_homotopyInvHomId (i : ι) : G i ≤ (G i).comap homotopyInvHomId

namespace FilteredHomotopyEquiv

variable {d : M →ₗ[S] M} {e : N →ₗ[S] N} {q : P →ₗ[S] P} {F : ι → Submodule S M}
  {G : ι → Submodule S N} {H : ι → Submodule S P}

/-! ### The equivalence relation -/

section Refl

variable (d F)

/-- The identity filtered chain homotopy equivalence, with zero homotopies. -/
def refl : FilteredHomotopyEquiv d d F F where
  hom := LinearMap.id
  inv := LinearMap.id
  homotopyHomInvId := 0
  homotopyInvHomId := 0
  hom_comm := by rw [id_comp, comp_id]
  inv_comm := by rw [id_comp, comp_id]
  homotopyHomInvId_comm := by simp
  homotopyInvHomId_comm := by simp
  le_comap_hom i := by rw [Submodule.comap_id]
  le_comap_inv i := by rw [Submodule.comap_id]
  le_comap_homotopyHomInvId i _ _ := zero_mem (F i)
  le_comap_homotopyInvHomId i _ _ := zero_mem (F i)

/-- The chain map `hom` of the identity equivalence is the identity. -/
@[simp]
theorem refl_hom : (refl d F).hom = LinearMap.id :=
  (rfl)

/-- The chain map `inv` of the identity equivalence is the identity. -/
@[simp]
theorem refl_inv : (refl d F).inv = LinearMap.id :=
  (rfl)

/-- The homotopy `homotopyHomInvId` of the identity equivalence vanishes. -/
@[simp]
theorem refl_homotopyHomInvId : (refl d F).homotopyHomInvId = 0 :=
  (rfl)

/-- The homotopy `homotopyInvHomId` of the identity equivalence vanishes. -/
@[simp]
theorem refl_homotopyInvHomId : (refl d F).homotopyInvHomId = 0 :=
  (rfl)

end Refl

section Symm

variable (E : FilteredHomotopyEquiv d e F G)

/-- The inverse of a filtered chain homotopy equivalence, exchanging the two chain maps and the two
homotopies. -/
def symm : FilteredHomotopyEquiv e d G F where
  hom := E.inv
  inv := E.hom
  homotopyHomInvId := E.homotopyInvHomId
  homotopyInvHomId := E.homotopyHomInvId
  hom_comm := E.inv_comm
  inv_comm := E.hom_comm
  homotopyHomInvId_comm := E.homotopyInvHomId_comm
  homotopyInvHomId_comm := E.homotopyHomInvId_comm
  le_comap_hom := E.le_comap_inv
  le_comap_inv := E.le_comap_hom
  le_comap_homotopyHomInvId := E.le_comap_homotopyInvHomId
  le_comap_homotopyInvHomId := E.le_comap_homotopyHomInvId

/-- The chain map `hom` of the inverse equivalence is `inv`. -/
@[simp]
theorem symm_hom : E.symm.hom = E.inv :=
  (rfl)

/-- The chain map `inv` of the inverse equivalence is `hom`. -/
@[simp]
theorem symm_inv : E.symm.inv = E.hom :=
  (rfl)

/-- The inverse equivalence exchanges the two homotopies. -/
@[simp]
theorem symm_homotopyHomInvId : E.symm.homotopyHomInvId = E.homotopyInvHomId :=
  (rfl)

/-- The inverse equivalence exchanges the two homotopies. -/
@[simp]
theorem symm_homotopyInvHomId : E.symm.homotopyInvHomId = E.homotopyHomInvId :=
  (rfl)

/-- The inverse of the inverse is the original equivalence. -/
@[simp]
theorem symm_symm : E.symm.symm = E :=
  (rfl)

end Symm

section Trans

variable (E : FilteredHomotopyEquiv d e F G) (E' : FilteredHomotopyEquiv e q G H)

/-- The composite of two filtered chain homotopy equivalences. -/
def trans : FilteredHomotopyEquiv d q F H where
  hom := E'.hom ∘ₗ E.hom
  inv := E.inv ∘ₗ E'.inv
  homotopyHomInvId := E.homotopyHomInvId + E.inv ∘ₗ E'.homotopyHomInvId ∘ₗ E.hom
  homotopyInvHomId := E'.homotopyInvHomId + E'.hom ∘ₗ E.homotopyInvHomId ∘ₗ E'.inv
  hom_comm := by rw [comp_assoc, E.hom_comm, ← comp_assoc, E'.hom_comm, comp_assoc]
  inv_comm := by rw [comp_assoc, E'.inv_comm, ← comp_assoc, E.inv_comm, comp_assoc]
  homotopyHomInvId_comm := comp_comp_sub_id_eq_of_sub_id_eq E.hom_comm E.inv_comm
    E.homotopyHomInvId_comm E'.homotopyHomInvId_comm
  homotopyInvHomId_comm := comp_comp_sub_id_eq_of_sub_id_eq E'.inv_comm E'.hom_comm
    E'.homotopyInvHomId_comm E.homotopyInvHomId_comm
  le_comap_hom i _ hx := E'.le_comap_hom i (E.le_comap_hom i hx)
  le_comap_inv i _ hx := E.le_comap_inv i (E'.le_comap_inv i hx)
  le_comap_homotopyHomInvId i _ hx := add_mem (E.le_comap_homotopyHomInvId i hx)
    (E.le_comap_inv i (E'.le_comap_homotopyHomInvId i (E.le_comap_hom i hx)))
  le_comap_homotopyInvHomId i _ hx := add_mem (E'.le_comap_homotopyInvHomId i hx)
    (E'.le_comap_hom i (E.le_comap_homotopyInvHomId i (E'.le_comap_inv i hx)))

/-- The chain map `hom` of a composite is the composite of the chain maps `hom`. -/
@[simp]
theorem trans_hom : (E.trans E').hom = E'.hom ∘ₗ E.hom :=
  (rfl)

/-- The chain map `inv` of a composite is the composite of the chain maps `inv`. -/
@[simp]
theorem trans_inv : (E.trans E').inv = E.inv ∘ₗ E'.inv :=
  (rfl)

/-- The homotopy `homotopyHomInvId` of a composite. -/
@[simp]
theorem trans_homotopyHomInvId :
    (E.trans E').homotopyHomInvId =
      E.homotopyHomInvId + E.inv ∘ₗ E'.homotopyHomInvId ∘ₗ E.hom :=
  (rfl)

/-- The homotopy `homotopyInvHomId` of a composite. -/
@[simp]
theorem trans_homotopyInvHomId :
    (E.trans E').homotopyInvHomId =
      E'.homotopyInvHomId + E'.hom ∘ₗ E.homotopyInvHomId ∘ₗ E'.inv :=
  (rfl)

end Trans

section OfLinearEquiv

variable (f : M ≃ₗ[S] N) (hf : f.toLinearMap ∘ₗ d = e ∘ₗ f.toLinearMap)
  (hFG : ∀ i, (F i).map f.toLinearMap = G i)

/-- A linear equivalence `f` intertwining `d` and `e` and carrying each level `F i` onto `G i` is
a filtered chain homotopy equivalence, with inverse `f.symm` and zero homotopies. -/
def ofLinearEquiv : FilteredHomotopyEquiv d e F G where
  hom := f.toLinearMap
  inv := f.symm.toLinearMap
  homotopyHomInvId := 0
  homotopyInvHomId := 0
  hom_comm := hf
  inv_comm := by
    ext y
    apply f.injective
    simpa using (congr($hf (f.symm y))).symm
  homotopyHomInvId_comm := by simp
  homotopyInvHomId_comm := by simp
  le_comap_hom i := by
    rw [← hFG i]
    exact Submodule.le_comap_map _ _
  le_comap_inv i := by rw [← hFG i, Submodule.map_equiv_eq_comap_symm]
  le_comap_homotopyHomInvId i _ _ := zero_mem (F i)
  le_comap_homotopyInvHomId i _ _ := zero_mem (G i)

/-- The chain map `hom` of `ofLinearEquiv f` is `f`. -/
@[simp]
theorem ofLinearEquiv_hom : (ofLinearEquiv f hf hFG).hom = f.toLinearMap :=
  (rfl)

/-- The chain map `inv` of `ofLinearEquiv f` is the inverse of `f`. -/
@[simp]
theorem ofLinearEquiv_inv : (ofLinearEquiv f hf hFG).inv = f.symm.toLinearMap :=
  (rfl)

/-- The homotopy `homotopyHomInvId` of `ofLinearEquiv f` vanishes. -/
@[simp]
theorem ofLinearEquiv_homotopyHomInvId : (ofLinearEquiv f hf hFG).homotopyHomInvId = 0 :=
  (rfl)

/-- The homotopy `homotopyInvHomId` of `ofLinearEquiv f` vanishes. -/
@[simp]
theorem ofLinearEquiv_homotopyInvHomId : (ofLinearEquiv f hf hFG).homotopyInvHomId = 0 :=
  (rfl)

end OfLinearEquiv

/-! ### Levels and quotients -/

section Level

variable (E : FilteredHomotopyEquiv d e F G) (j : ι) (hF : F j ≤ (F j).comap d)
  (hG : G j ≤ (G j).comap e)

/-- The restriction of a filtered chain homotopy equivalence to the levels `F j` and `G j`, when
`d` preserves `F j` and `e` preserves `G j`. It is filtered by the traces `F i ∩ F j` and
`G i ∩ G j` of the filtrations on these levels. -/
def restrict :
    FilteredHomotopyEquiv (d.restrict hF) (e.restrict hG) (fun i ↦ (F i).comap (F j).subtype)
      (fun i ↦ (G i).comap (G j).subtype) where
  hom := E.hom.restrict (E.le_comap_hom j)
  inv := E.inv.restrict (E.le_comap_inv j)
  homotopyHomInvId := E.homotopyHomInvId.restrict (E.le_comap_homotopyHomInvId j)
  homotopyInvHomId := E.homotopyInvHomId.restrict (E.le_comap_homotopyInvHomId j)
  hom_comm := by
    ext x
    simpa using congr($E.hom_comm x)
  inv_comm := by
    ext x
    simpa using congr($E.inv_comm x)
  homotopyHomInvId_comm := by
    ext x
    simpa using congr($E.homotopyHomInvId_comm x)
  homotopyInvHomId_comm := by
    ext x
    simpa using congr($E.homotopyInvHomId_comm x)
  le_comap_hom i _ hx := E.le_comap_hom i hx
  le_comap_inv i _ hx := E.le_comap_inv i hx
  le_comap_homotopyHomInvId i _ hx := E.le_comap_homotopyHomInvId i hx
  le_comap_homotopyInvHomId i _ hx := E.le_comap_homotopyInvHomId i hx

/-- The chain map `hom` of the restriction is the restriction of `hom`. -/
@[simp]
theorem restrict_hom : (E.restrict j hF hG).hom = E.hom.restrict (E.le_comap_hom j) :=
  (rfl)

/-- The chain map `inv` of the restriction is the restriction of `inv`. -/
@[simp]
theorem restrict_inv : (E.restrict j hF hG).inv = E.inv.restrict (E.le_comap_inv j) :=
  (rfl)

/-- The homotopy `homotopyHomInvId` of the restriction is the restriction of `homotopyHomInvId`. -/
@[simp]
theorem restrict_homotopyHomInvId :
    (E.restrict j hF hG).homotopyHomInvId =
      E.homotopyHomInvId.restrict (E.le_comap_homotopyHomInvId j) :=
  (rfl)

/-- The homotopy `homotopyInvHomId` of the restriction is the restriction of `homotopyInvHomId`. -/
@[simp]
theorem restrict_homotopyInvHomId :
    (E.restrict j hF hG).homotopyInvHomId =
      E.homotopyInvHomId.restrict (E.le_comap_homotopyInvHomId j) :=
  (rfl)

/-- The filtered chain homotopy equivalence induced on the quotients `M ⧸ F j` and `N ⧸ G j`,
when `d` preserves `F j` and `e` preserves `G j`. It is filtered by the images of the
filtrations. -/
def quotient :
    FilteredHomotopyEquiv ((F j).mapQ (F j) d hF) ((G j).mapQ (G j) e hG)
      (fun i ↦ (F i).map (F j).mkQ) (fun i ↦ (G i).map (G j).mkQ) where
  hom := (F j).mapQ (G j) E.hom (E.le_comap_hom j)
  inv := (G j).mapQ (F j) E.inv (E.le_comap_inv j)
  homotopyHomInvId := (F j).mapQ (F j) E.homotopyHomInvId (E.le_comap_homotopyHomInvId j)
  homotopyInvHomId := (G j).mapQ (G j) E.homotopyInvHomId (E.le_comap_homotopyInvHomId j)
  hom_comm := by
    ext x
    simpa using congr(Submodule.Quotient.mk (p := G j) ($E.hom_comm x))
  inv_comm := by
    ext x
    simpa using congr(Submodule.Quotient.mk (p := F j) ($E.inv_comm x))
  homotopyHomInvId_comm := by
    ext x
    simpa using congr(Submodule.Quotient.mk (p := F j) ($E.homotopyHomInvId_comm x))
  homotopyInvHomId_comm := by
    ext x
    simpa using congr(Submodule.Quotient.mk (p := G j) ($E.homotopyInvHomId_comm x))
  le_comap_hom i := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨E.hom x, E.le_comap_hom i hx, rfl⟩
  le_comap_inv i := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨E.inv x, E.le_comap_inv i hx, rfl⟩
  le_comap_homotopyHomInvId i := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨E.homotopyHomInvId x, E.le_comap_homotopyHomInvId i hx, rfl⟩
  le_comap_homotopyInvHomId i := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨E.homotopyInvHomId x, E.le_comap_homotopyInvHomId i hx, rfl⟩

/-- The chain map `hom` on the quotients is induced by `hom`. -/
@[simp]
theorem quotient_hom : (E.quotient j hF hG).hom = (F j).mapQ (G j) E.hom (E.le_comap_hom j) :=
  (rfl)

/-- The chain map `inv` on the quotients is induced by `inv`. -/
@[simp]
theorem quotient_inv : (E.quotient j hF hG).inv = (G j).mapQ (F j) E.inv (E.le_comap_inv j) :=
  (rfl)

/-- The homotopy `homotopyHomInvId` on the quotients is induced by `homotopyHomInvId`. -/
@[simp]
theorem quotient_homotopyHomInvId :
    (E.quotient j hF hG).homotopyHomInvId =
      (F j).mapQ (F j) E.homotopyHomInvId (E.le_comap_homotopyHomInvId j) :=
  (rfl)

/-- The homotopy `homotopyInvHomId` on the quotients is induced by `homotopyInvHomId`. -/
@[simp]
theorem quotient_homotopyInvHomId :
    (E.quotient j hF hG).homotopyInvHomId =
      (G j).mapQ (G j) E.homotopyInvHomId (E.le_comap_homotopyInvHomId j) :=
  (rfl)

end Level

/-! ### Homology -/

section Homology

variable (E : FilteredHomotopyEquiv d e F G) (hd : d ∘ₗ d = 0) (he : e ∘ₗ e = 0)

/-- The isomorphism of homologies induced by a filtered chain homotopy equivalence between
square-zero endomorphisms: the maps induced by the two chain maps are mutually inverse, since the
chain homotopies make their composites homotopic to the identities. -/
noncomputable def homologyEquiv : d.homology hd ≃ₗ[S] e.homology he :=
  LinearEquiv.ofLinearMap (homologyMap E.hom hd he E.hom_comm) (homologyMap E.inv he hd E.inv_comm)
    (by
      rw [homologyMap_comp_homologyMap,
        homologyMap_eq_of_sub_eq _ _ _ he he _ (by simp) E.homotopyInvHomId_comm, homologyMap_id])
    (by
      rw [homologyMap_comp_homologyMap,
        homologyMap_eq_of_sub_eq _ _ _ hd hd _ (by simp) E.homotopyHomInvId_comm, homologyMap_id])

/-- The isomorphism of homologies is the map induced by the chain map `hom`. -/
@[simp]
theorem homologyEquiv_apply (c : d.homology hd) :
    E.homologyEquiv hd he c = homologyMap E.hom hd he E.hom_comm c :=
  (rfl)

/-- The inverse isomorphism of homologies is the map induced by the chain map `inv`. -/
@[simp]
theorem homologyEquiv_symm_apply (c : e.homology he) :
    (E.homologyEquiv hd he).symm c = homologyMap E.inv he hd E.inv_comm c :=
  (rfl)

/-- The inverse equivalence induces the inverse isomorphism of homologies. -/
@[simp]
theorem homologyEquiv_symm : E.symm.homologyEquiv he hd = (E.homologyEquiv hd he).symm :=
  (rfl)

variable (d F) in
/-- The identity induces the identity on homology. -/
@[simp]
theorem homologyEquiv_refl :
    (refl d F).homologyEquiv hd hd = LinearEquiv.refl S (d.homology hd) := by
  ext c
  simp

/-- A composite of equivalences induces the composite of the isomorphisms of homologies. -/
@[simp]
theorem homologyEquiv_trans (E' : FilteredHomotopyEquiv e q G H) (hq : q ∘ₗ q = 0) :
    (E.trans E').homologyEquiv hd hq = (E.homologyEquiv hd he).trans (E'.homologyEquiv he hq) := by
  ext c
  simp

/-- The filtered chain homotopy equivalence of a filtered isomorphism of complexes `f` induces the
isomorphism of homologies `LinearEquiv.homologyEquiv` of `f`. -/
@[simp]
theorem homologyEquiv_ofLinearEquiv (f : M ≃ₗ[S] N) (hf : f.toLinearMap ∘ₗ d = e ∘ₗ f.toLinearMap)
    (hFG : ∀ i, (F i).map f.toLinearMap = G i) :
    (ofLinearEquiv f hf hFG).homologyEquiv hd he = f.homologyEquiv hd he hf := by
  ext c
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  simp

variable {i j : ι} (hFi : F i ≤ (F i).comap d) (hFj : F j ≤ (F j).comap d)
  (hGi : G i ≤ (G i).comap e) (hGj : G j ≤ (G j).comap e)

/-- The isomorphism between the homologies of the subquotients `F j ⧸ (F i ∩ F j)` and
`G j ⧸ (G i ∩ G j)`, that is, `F j ⧸ F i` and `G j ⧸ G i` when `F i ≤ F j` and `G i ≤ G j`,
induced by a filtered chain homotopy equivalence between square-zero endomorphisms preserving
the levels `F i`, `F j`, `G i` and `G j`. For a filtration indexed by `ℤ`, the subquotients
`F a ⧸ F (a - 1)` are the pieces of the associated graded complex. -/
noncomputable def subquotientHomologyEquiv :
    (d.restrict hFj).quotientHomology (d.restrict_comp_restrict_eq_zero hd (F j) hFj)
        ((F i).comap (F j).subtype) (comap_subtype_le_comap_restrict hFi hFj) ≃ₗ[S]
      (e.restrict hGj).quotientHomology (e.restrict_comp_restrict_eq_zero he (G j) hGj)
        ((G i).comap (G j).subtype) (comap_subtype_le_comap_restrict hGi hGj) :=
  ((E.restrict j hFj hGj).quotient i (comap_subtype_le_comap_restrict hFi hFj)
    (comap_subtype_le_comap_restrict hGi hGj)).homologyEquiv _ _

/-- The isomorphism of the homologies of the subquotients sends the class of `m ∈ F j` with
`d m ∈ F i` to the class of `hom m`. This is stated with `quotientHomologyClass`, for rewriting;
`simp` unfolds `quotientHomologyClass` instead. -/
theorem subquotientHomologyEquiv_quotientHomologyClass (m : F j)
    (hm : d.restrict hFj m ∈ (F i).comap (F j).subtype) :
    E.subquotientHomologyEquiv hd he hFi hFj hGi hGj (quotientHomologyClass _ _ m hm) =
      quotientHomologyClass _ _ (E.hom.restrict (E.le_comap_hom j) m) (by
        have h : E.hom (d m) ∈ G i := E.le_comap_hom i hm
        have h' : E.hom (d m) = e (E.hom m) := congr($E.hom_comm (m : M))
        simpa [h'] using h) := by
  rw [subquotientHomologyEquiv, homologyEquiv_apply, quotientHomologyClass_def,
    quotientHomologyClass_def, homologyMap_mk]
  simp only [quotient_hom, restrict_hom, Submodule.mapQ_apply]

/-- The inverse isomorphism of the homologies of the subquotients sends the class of `n ∈ G j`
with `e n ∈ G i` to the class of `inv n`. This is stated with `quotientHomologyClass`, for
rewriting; `simp` unfolds `quotientHomologyClass` instead. -/
theorem subquotientHomologyEquiv_symm_quotientHomologyClass (n : G j)
    (hn : e.restrict hGj n ∈ (G i).comap (G j).subtype) :
    (E.subquotientHomologyEquiv hd he hFi hFj hGi hGj).symm (quotientHomologyClass _ _ n hn) =
      quotientHomologyClass _ _ (E.inv.restrict (E.le_comap_inv j) n) (by
        have h : E.inv (e n) ∈ F i := E.le_comap_inv i hn
        have h' : E.inv (e n) = d (E.inv n) := congr($E.inv_comm (n : N))
        simpa [h'] using h) := by
  rw [subquotientHomologyEquiv, homologyEquiv_symm_apply, quotientHomologyClass_def,
    quotientHomologyClass_def, homologyMap_mk]
  simp only [quotient_inv, restrict_inv, Submodule.mapQ_apply]

end Homology

end FilteredHomotopyEquiv

end LinearMap
