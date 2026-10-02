/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.NumberedFiber
public import TauCeti.Topology.Homotopy.Monodromy.Functoriality

/-!
# Pulling connected covers back along a homeomorphism of the base

A homeomorphism `h : X ≃ₜ Y` pulls a covering space `p : E → Y` back to the covering space
`h.symm ∘ p : E → X` of `X`, with the same total space. This file packages that operation on the
connected covering spaces of `TauCeti.Topology.Covering.Category` and on the three rigidified
carriers of `TauCeti.AlgebraicTopology.UniversalCover.Classification.NumberedFiber`, and computes
its effect on monodromy.

* `TauCeti.ConnectedCoveringSpace.pullback h` is the functor `ConnectedCoveringSpace Y ⥤
  ConnectedCoveringSpace X`; it keeps the total space and the maps of total spaces, and composes
  the projection with `h.symm`. Pulling back along the identity is the identity functor, and
  pulling back along a composite is the composite of the pullbacks in the reverse order
  (`TauCeti.ConnectedCoveringSpace.pullback_refl`, `TauCeti.ConnectedCoveringSpace.pullback_trans`),
  so the self-homeomorphisms of `X` act on its covers through this functor.
* When `h x = y`, the fibre of the pulled-back cover over `x` is the fibre of the original cover
  over `y` (`TauCeti.ConnectedCoveringSpace.pullbackFiberEquiv`), and under that identification the
  monodromy of the pullback along a loop `γ` at `x` is the monodromy of the original cover along
  the image loop `h ∘ γ` at `y` (`TauCeti.ConnectedCoveringSpace.pullbackFiberEquiv_monodromy`).
  Pulling back is contravariant: the cover of `X` sees `π₁(X, x)` through the isomorphism
  `π₁(X, x) ≃* π₁(Y, y)` induced by `h`.
* Consequently a fibre-numbered cover of `(Y, y)` pulls back to a fibre-numbered cover of
  `(X, x)` whose numbered monodromy representation is the original one precomposed with that
  isomorphism (`TauCeti.ConnectedFiberNumberedCover.permCongrHom_comp_monodromyPerm_pullback`), a
  pointed cover pulls back to a pointed cover, and a bare cover to a bare cover. Pullback descends
  to the isomorphism classes of all three kinds of covers, satisfies the identity and composition
  laws on the nose at every level, and commutes with relabelling and with the forgetful maps
  between the levels.

For the thrice-punctured sphere this is how the anharmonic self-homeomorphisms act on covers: the
pullback along `z ↦ 1 − z`, which fixes the basepoint, realizes the exchange of the branch points
`0` and `1` on monodromy triples.

## Main declarations

* `TauCeti.ConnectedCoveringSpace.pullback`: the pullback functor along a homeomorphism of bases,
  with `TauCeti.ConnectedCoveringSpace.pullback_refl` and
  `TauCeti.ConnectedCoveringSpace.pullback_trans`.
* `TauCeti.ConnectedCoveringSpace.pullbackFiberEquiv`,
  `TauCeti.ConnectedCoveringSpace.pullbackFiberEquiv_monodromy`: the fibre identification and its
  compatibility with monodromy.
* `TauCeti.ConnectedFiberNumberedCover.pullback`, `TauCeti.ConnectedPointedCover.pullback`,
  `TauCeti.ConnectedCover.pullback`: pullback of numbered, of pointed and of bare covers, with
  `TauCeti.ConnectedFiberNumberedCover.permCongrHom_comp_monodromyPerm_pullback` computing the
  numbered monodromy of the pullback, and the laws `pullback_refl` and `pullback_pullback` in each
  namespace.
* `TauCeti.ConnectedFiberNumberedCoverClass.pullback`,
  `TauCeti.ConnectedPointedCoverClass.pullback`, `TauCeti.ConnectedCoverClass.pullback`: the
  descended maps on isomorphism classes, with their
  `pullback_mk`, `pullback_refl` and `pullback_pullback` lemmas and the compatibilities
  `TauCeti.ConnectedFiberNumberedCoverClass.pullback_smul`,
  `TauCeti.ConnectedFiberNumberedCoverClass.markLabel_pullback`,
  `TauCeti.ConnectedFiberNumberedCoverClass.forgetNumbering_pullback` and
  `TauCeti.ConnectedPointedCoverClass.forgetPoint_pullback`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.3 (change of base for
  covering spaces and the action of the fundamental group on a fibre).
-/

public section

open CategoryTheory Equiv

universe u

namespace TauCeti

variable {X Y Z : TopCat.{u}}

namespace ConnectedCoveringSpace

/-- The pullback of connected covering spaces along a homeomorphism `h : X ≃ₜ Y` of bases: the
total space is unchanged and the projection is composed with `h.symm`. On morphisms it is the
identity on maps of total spaces. -/
-- The total space of the pullback must be visible as the original total space: the statements of
-- `pullback_obj_proj_apply`, `pullback_map_hom_left` and `pullbackFiberEquiv_apply_coe` apply the
-- original projection and maps to points of the pullback, and do not typecheck when this
-- definition is sealed ("definitions were not unfolded because their definition is not exposed").
@[expose] def pullback (h : X ≃ₜ Y) : ConnectedCoveringSpace Y ⥤ ConnectedCoveringSpace X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Over.map (TopCat.ofHom (h.symm : C(Y, X))))
    fun c => ⟨Over.isCoveringMap_iff.2 (c.isCoveringMap_proj.homeomorph_comp h.symm),
      c.connectedSpace⟩

variable (h : X ≃ₜ Y) (c : ConnectedCoveringSpace Y)

/-- The projection of the pullback is the original projection followed by `h.symm`. -/
@[simp]
theorem pullback_obj_proj_apply (e : ((pullback h).obj c : TopCat)) :
    ((pullback h).obj c).proj e = h.symm (c.proj e) :=
  (rfl)

/-- The pullback functor acts on morphisms by the same map of total spaces. -/
@[simp]
theorem pullback_map_hom_left {c c' : ConnectedCoveringSpace Y} (f : c ⟶ c') :
    ((pullback h).map f).hom.left = f.hom.left :=
  (rfl)

/-- Pulling back along the identity is the identity functor. -/
@[simp]
theorem pullback_refl : pullback (Homeomorph.refl X) = 𝟭 (ConnectedCoveringSpace X) :=
  (rfl)

/-- Pulling back along a composite homeomorphism is the composite of the pullbacks, in the reverse
order. -/
@[simp]
theorem pullback_trans (h' : Y ≃ₜ Z) : pullback (h.trans h') = pullback h' ⋙ pullback h :=
  (rfl)

variable {x : X} {y : Y} (hx : h x = y)

/-- When `h x = y`, the fibre of the pullback over `x` is the fibre of the original cover over
`y`: both are the same subset of the common total space. -/
def pullbackFiberEquiv : ⇑((pullback h).obj c).proj ⁻¹' {x} ≃ ⇑c.proj ⁻¹' {y} :=
  Equiv.subtypeEquivRight fun e =>
    (h.symm_apply_eq.trans (by rw [hx]) : h.symm (c.proj e) = x ↔ c.proj e = y)

/-- On underlying points, the fibre identification of the pullback is the identity. -/
@[simp]
theorem pullbackFiberEquiv_apply_coe (e : ⇑((pullback h).obj c).proj ⁻¹' {x}) :
    (pullbackFiberEquiv h c hx e : (c : TopCat)) = (e : ((pullback h).obj c : TopCat)) :=
  (rfl)

/-- On underlying points, the inverse fibre identification of the pullback is the identity. -/
@[simp]
theorem pullbackFiberEquiv_symm_apply_coe (e : ⇑c.proj ⁻¹' {y}) :
    ((pullbackFiberEquiv h c hx).symm e : ((pullback h).obj c : TopCat)) = (e : (c : TopCat)) :=
  (rfl)

/-- **The monodromy of a pullback is the monodromy along the image loop.** Under the fibre
identification, the pullback along `h` transports a point of the fibre along a loop `γ` at `x`
exactly as the original cover transports it along `h ∘ γ` at `y`. -/
theorem pullbackFiberEquiv_monodromy (γ : FundamentalGroup X x)
    (e : ⇑((pullback h).obj c).proj ⁻¹' {x}) :
    pullbackFiberEquiv h c hx (((pullback h).obj c).isCoveringMap_proj.monodromy γ e) =
      c.isCoveringMap_proj.monodromy
        (FundamentalGroup.homeomorphMulEquivOfEq h hx γ : FundamentalGroup Y y)
        (pullbackFiberEquiv h c hx e) := by
  subst hx
  -- `Equiv.compFiberEquiv_monodromy` is this statement for the fibre over `h.symm.symm x` and the
  -- image loop `γ.map h.symm.symm`; these agree with the fibre over `h x` and the image of `γ`
  -- under the induced isomorphism definitionally, but not syntactically, so the comparison is
  -- assembled in term mode rather than by rewriting.
  have key := congrArg Subtype.val
    (c.isCoveringMap_proj.compFiberEquiv_monodromy h.symm (γ : Path.Homotopic.Quotient x x) e)
  have hpt (z : ⇑((pullback h).obj c).proj ⁻¹' {x}) :
      (Equiv.compFiberEquiv (p := ⇑c.proj) h.symm.toEquiv x z : (c : TopCat)) =
        (pullbackFiberEquiv h c rfl z : (c : TopCat)) :=
    (Equiv.compFiberEquiv_apply_coe _ _ _).trans (pullbackFiberEquiv_apply_coe h c rfl z).symm
  have hΦ : Equiv.compFiberEquiv (p := ⇑c.proj) h.symm.toEquiv x e = pullbackFiberEquiv h c rfl e :=
    Subtype.ext (hpt e)
  have hpath :
      Path.Homotopic.Quotient.map (γ : Path.Homotopic.Quotient x x) (h.symm.symm : C(X, Y)) =
        (FundamentalGroup.homeomorphMulEquivOfEq h rfl γ : FundamentalGroup Y (h x)) := by
    rw [FundamentalGroup.homeomorphMulEquivOfEq_apply, FundamentalGroup.mapOfEq_apply]
    exact (Path.Homotopic.Quotient.cast_rfl_rfl _).symm
  refine Subtype.ext (((hpt _).symm.trans key).trans ?_)
  exact congrArg Subtype.val
    (congrArg₂ (fun a z => c.isCoveringMap_proj.monodromy a z) hpath hΦ)

end ConnectedCoveringSpace

variable (h : X ≃ₜ Y) (h' : Y ≃ₜ Z) {x : X} {y : Y} {z : Z} (hx : h x = y) (hy : h' y = z) {n : ℕ}

/-! ### Fibre-numbered covers -/

namespace ConnectedFiberNumberedCover

/-- The pullback of a fibre-numbered cover of `(Y, y)` along a homeomorphism `h` with `h x = y`:
the pulled-back cover, with the fibre over `x` numbered through the fibre over `y`. -/
-- The type of `ν` depends on the projected cover, so the statement of `pullback_ν` typechecks only
-- when this definition is exposed.
@[expose] def pullback (c : ConnectedFiberNumberedCover y n) : ConnectedFiberNumberedCover x n where
  cover := (ConnectedCoveringSpace.pullback h).obj c.cover
  ν := (ConnectedCoveringSpace.pullbackFiberEquiv h c.cover hx).trans c.ν

variable (c : ConnectedFiberNumberedCover y n)

@[simp]
theorem pullback_cover :
    (c.pullback h hx).cover = (ConnectedCoveringSpace.pullback h).obj c.cover :=
  (rfl)

@[simp]
theorem pullback_ν :
    (c.pullback h hx).ν = (ConnectedCoveringSpace.pullbackFiberEquiv h c.cover hx).trans c.ν :=
  (rfl)

/-- **The numbered monodromy of a pullback is the numbered monodromy precomposed with the induced
isomorphism of fundamental groups.** -/
theorem permCongrHom_comp_monodromyPerm_pullback :
    (c.pullback h hx).ν.permCongrHom.toMonoidHom.comp
        ((c.pullback h hx).cover.isCoveringMap_proj.monodromyPerm x) =
      (c.ν.permCongrHom.toMonoidHom.comp (c.cover.isCoveringMap_proj.monodromyPerm y)).comp
        (FundamentalGroup.homeomorphMulEquivOfEq h hx).toMonoidHom := by
  refine MonoidHom.ext fun γ => Equiv.ext fun i => ?_
  -- Unfolding the transported permutations, the left side is `c.ν (Φ (γ • Φ.symm (c.ν.symm i)))`
  -- and the right side is `c.ν (h γ • c.ν.symm i)`, for the fibre identification `Φ`, which
  -- intertwines the two monodromy actions. The two sides are compared by `exact` because the fibre
  -- of the pullback appears in the types with the numbering unfolded on one side and not the other.
  exact congrArg c.ν
    ((ConnectedCoveringSpace.pullbackFiberEquiv_monodromy h c.cover hx γ _).trans
      (congrArg (c.cover.isCoveringMap_proj.monodromy _)
        ((ConnectedCoveringSpace.pullbackFiberEquiv h c.cover hx).apply_symm_apply _)))

/-- Relabelling commutes with pullback. -/
@[simp]
theorem pullback_smul (τ : Perm (Fin n)) : (τ • c).pullback h hx = τ • c.pullback h hx :=
  (rfl)

-- Here and in the `pullback_refl` lemmas below, `(y := x)` pins the target point: a bare `rfl`
-- would elaborate it as `Homeomorph.refl X x`, and the generic `pullback` lemmas then no longer
-- rewrite the resulting term.
/-- Pulling back along the identity changes nothing. -/
@[simp]
theorem pullback_refl (c : ConnectedFiberNumberedCover x n) :
    c.pullback (Homeomorph.refl X) (y := x) rfl = c :=
  (rfl)

/-- Pulling back twice is pulling back along the composite homeomorphism. -/
@[simp]
theorem pullback_pullback (c : ConnectedFiberNumberedCover z n) :
    (c.pullback h' hy).pullback h hx =
      c.pullback (h.trans h') ((h.trans_apply h' x).trans ((congrArg h' hx).trans hy)) :=
  (rfl)

end ConnectedFiberNumberedCover

/-- A label-preserving isomorphism of numbered covers pulls back to one. -/
theorem ConnectedFiberNumberedCoverIso.pullback {c c' : ConnectedFiberNumberedCover y n}
    (hcc : ConnectedFiberNumberedCoverIso c c') :
    ConnectedFiberNumberedCoverIso (c.pullback h hx) (c'.pullback h hx) := by
  obtain ⟨f, hf⟩ := connectedFiberNumberedCoverIso_iff_exists.1 hcc
  exact connectedFiberNumberedCoverIso_iff_exists.2
    ⟨(ConnectedCoveringSpace.pullback h).mapIso f, hf⟩

namespace ConnectedFiberNumberedCoverClass

/-- Pullback along `h`, on isomorphism classes of fibre-numbered covers. -/
def pullback : ConnectedFiberNumberedCoverClass y n → ConnectedFiberNumberedCoverClass x n :=
  lift (fun c => mk (c.pullback h hx)) fun _ _ hcc => mk_eq_mk_iff.2 (hcc.pullback h hx)

@[simp]
theorem pullback_mk (c : ConnectedFiberNumberedCover y n) :
    (mk c).pullback h hx = mk (c.pullback h hx) :=
  lift_mk _ _ c

/-- Relabelling commutes with pullback on classes. -/
@[simp]
theorem pullback_smul (τ : Perm (Fin n)) (C : ConnectedFiberNumberedCoverClass y n) :
    (τ • C).pullback h hx = τ • C.pullback h hx :=
  ind (fun c => by rw [smul_mk, pullback_mk, pullback_mk, smul_mk,
    ConnectedFiberNumberedCover.pullback_smul]) C

/-- Pulling back along the identity changes nothing, on classes. -/
@[simp]
theorem pullback_refl (C : ConnectedFiberNumberedCoverClass x n) :
    C.pullback (Homeomorph.refl X) (y := x) rfl = C :=
  ind (fun c =>
    (pullback_mk _ _ c).trans (congrArg mk (ConnectedFiberNumberedCover.pullback_refl c))) C

/-- Pulling back twice is pulling back along the composite homeomorphism, on classes. -/
@[simp]
theorem pullback_pullback (C : ConnectedFiberNumberedCoverClass z n) :
    (C.pullback h' hy).pullback h hx =
      C.pullback (h.trans h') ((h.trans_apply h' x).trans ((congrArg h' hx).trans hy)) :=
  ind (fun c => by
    rw [pullback_mk, pullback_mk, pullback_mk, ConnectedFiberNumberedCover.pullback_pullback]) C

end ConnectedFiberNumberedCoverClass

/-! ### Pointed covers -/

namespace ConnectedPointedCover

/-- The pullback of a pointed cover of `(Y, y)` along a homeomorphism `h` with `h x = y`: the
pulled-back cover, pointed at the same point, which lies over `x` in the pullback. -/
-- The type of `e` depends on the projected cover, so the statement of `pullback_e` typechecks only
-- when this definition is exposed.
@[expose] def pullback (c : ConnectedPointedCover y n) : ConnectedPointedCover x n where
  cover := (ConnectedCoveringSpace.pullback h).obj c.cover
  e := (ConnectedCoveringSpace.pullbackFiberEquiv h c.cover hx).symm c.e
  nonempty_equiv_fin :=
    c.nonempty_equiv_fin.map fun ν =>
      (ConnectedCoveringSpace.pullbackFiberEquiv h c.cover hx).trans ν

variable (c : ConnectedPointedCover y n)

@[simp]
theorem pullback_cover :
    (c.pullback h hx).cover = (ConnectedCoveringSpace.pullback h).obj c.cover :=
  (rfl)

@[simp]
theorem pullback_e :
    (c.pullback h hx).e = (ConnectedCoveringSpace.pullbackFiberEquiv h c.cover hx).symm c.e :=
  (rfl)

/-- Pulling back along the identity changes nothing. -/
@[simp]
theorem pullback_refl (c : ConnectedPointedCover x n) :
    c.pullback (Homeomorph.refl X) (y := x) rfl = c :=
  (rfl)

/-- Pulling back twice is pulling back along the composite homeomorphism. -/
@[simp]
theorem pullback_pullback (c : ConnectedPointedCover z n) :
    (c.pullback h' hy).pullback h hx =
      c.pullback (h.trans h') ((h.trans_apply h' x).trans ((congrArg h' hx).trans hy)) :=
  (rfl)

end ConnectedPointedCover

/-- Marking a label commutes with pullback. -/
@[simp]
theorem ConnectedFiberNumberedCover.markLabel_pullback (c : ConnectedFiberNumberedCover y n)
    (i : Fin n) : (c.pullback h hx).markLabel i = (c.markLabel i).pullback h hx :=
  (rfl)

/-- A pointed isomorphism of pointed covers pulls back to one. -/
theorem ConnectedPointedCoverIso.pullback {c c' : ConnectedPointedCover y n}
    (hcc : ConnectedPointedCoverIso c c') :
    ConnectedPointedCoverIso (c.pullback h hx) (c'.pullback h hx) := by
  obtain ⟨f, hf⟩ := connectedPointedCoverIso_iff_exists.1 hcc
  exact connectedPointedCoverIso_iff_exists.2 ⟨(ConnectedCoveringSpace.pullback h).mapIso f, hf⟩

namespace ConnectedPointedCoverClass

open ConnectedFiberNumberedCoverClass

/-- Pullback along `h`, on isomorphism classes of pointed covers: pull back the class of any
numbering of the cover and mark the label of the chosen point again. This does not depend on the
numbering because pullback commutes with relabelling
(`TauCeti.ConnectedFiberNumberedCoverClass.pullback_smul`), and it is characterized by
`TauCeti.ConnectedFiberNumberedCoverClass.markLabel_pullback` and `pullback_mk`. -/
noncomputable def pullback (C : ConnectedPointedCoverClass y n) : ConnectedPointedCoverClass x n :=
  Quotient.lift (s := MulAction.orbitRel (Perm (Fin n)) _)
    (fun Ni : ConnectedFiberNumberedCoverClass y n × Fin n => (Ni.1.pullback h hx).markLabel Ni.2)
    (fun _ Ni' hNN' => by
      obtain ⟨τ, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hNN')
      rw [Prod.smul_fst, Prod.smul_snd, pullback_smul, markLabel_smul, Perm.smul_def,
        symm_apply_apply])
    (markedOrbitRelQuotientEquiv.symm C)

end ConnectedPointedCoverClass

/-- Marking a label commutes with pullback, on classes. -/
@[simp]
theorem ConnectedFiberNumberedCoverClass.markLabel_pullback
    (C : ConnectedFiberNumberedCoverClass y n) (i : Fin n) :
    (C.pullback h hx).markLabel i = (C.markLabel i).pullback h hx := by
  rw [ConnectedPointedCoverClass.pullback, markedOrbitRelQuotientEquiv_symm_markLabel]
  rfl

/-- The pullback of the class of a pointed cover is the class of its pullback. -/
@[simp]
theorem ConnectedPointedCoverClass.pullback_mk (c : ConnectedPointedCover y n) :
    (mk c).pullback h hx = mk (c.pullback h hx) := by
  obtain ⟨N, i, hN⟩ := (mk c).exists_markLabel_eq
  obtain ⟨c₀, rfl⟩ := ConnectedFiberNumberedCoverClass.mk_surjective N
  rw [ConnectedFiberNumberedCoverClass.markLabel_mk] at hN
  rw [← hN, ← ConnectedFiberNumberedCoverClass.markLabel_mk,
    ← ConnectedFiberNumberedCoverClass.markLabel_pullback,
    ConnectedFiberNumberedCoverClass.pullback_mk, ConnectedFiberNumberedCoverClass.markLabel_mk,
    ConnectedFiberNumberedCover.markLabel_pullback, mk_eq_mk_iff]
  exact (mk_eq_mk_iff.1 hN).pullback h hx

namespace ConnectedPointedCoverClass

/-- Pulling back along the identity changes nothing, on classes. -/
@[simp]
theorem pullback_refl (C : ConnectedPointedCoverClass x n) :
    C.pullback (Homeomorph.refl X) (y := x) rfl = C := by
  obtain ⟨c, rfl⟩ := mk_surjective C
  exact (pullback_mk _ _ c).trans (congrArg mk (ConnectedPointedCover.pullback_refl c))

/-- Pulling back twice is pulling back along the composite homeomorphism, on classes. -/
@[simp]
theorem pullback_pullback (C : ConnectedPointedCoverClass z n) :
    (C.pullback h' hy).pullback h hx =
      C.pullback (h.trans h') ((h.trans_apply h' x).trans ((congrArg h' hx).trans hy)) := by
  obtain ⟨c, rfl⟩ := mk_surjective C
  rw [pullback_mk, pullback_mk, pullback_mk, ConnectedPointedCover.pullback_pullback]

end ConnectedPointedCoverClass

/-! ### Bare covers -/

namespace ConnectedCover

/-- The pullback of a bare cover of `(Y, y)` of degree `n` along a homeomorphism `h` with
`h x = y`, a bare cover of `(X, x)` of degree `n`. -/
def pullback (c : ConnectedCover y n) : ConnectedCover x n where
  cover := (ConnectedCoveringSpace.pullback h).obj c.cover
  nonempty_equiv_fin :=
    c.nonempty_equiv_fin.map fun ν =>
      (ConnectedCoveringSpace.pullbackFiberEquiv h c.cover hx).trans ν

@[simp]
theorem pullback_cover (c : ConnectedCover y n) :
    (c.pullback h hx).cover = (ConnectedCoveringSpace.pullback h).obj c.cover :=
  (rfl)

/-- Pulling back along the identity changes nothing. -/
@[simp]
theorem pullback_refl (c : ConnectedCover x n) :
    c.pullback (Homeomorph.refl X) (y := x) rfl = c :=
  (rfl)

/-- Pulling back twice is pulling back along the composite homeomorphism. -/
@[simp]
theorem pullback_pullback (c : ConnectedCover z n) :
    (c.pullback h' hy).pullback h hx =
      c.pullback (h.trans h') ((h.trans_apply h' x).trans ((congrArg h' hx).trans hy)) :=
  (rfl)

/-- Forgetting the numbering commutes with pullback. -/
@[simp]
theorem _root_.TauCeti.ConnectedFiberNumberedCover.forgetNumbering_pullback
    (c : ConnectedFiberNumberedCover y n) :
    (c.pullback h hx).forgetNumbering = c.forgetNumbering.pullback h hx :=
  ConnectedCover.ext (by simp)

/-- Forgetting the chosen point commutes with pullback. -/
@[simp]
theorem _root_.TauCeti.ConnectedPointedCover.forgetPoint_pullback (c : ConnectedPointedCover y n) :
    (c.pullback h hx).forgetPoint = c.forgetPoint.pullback h hx :=
  ConnectedCover.ext (by simp)

end ConnectedCover

namespace ConnectedCoverClass

open ConnectedFiberNumberedCoverClass

/-- Pullback along `h`, on isomorphism classes of bare covers: pull back the class of any numbering
of the cover and forget the numbering again. This does not depend on the numbering because pullback
commutes with relabelling (`TauCeti.ConnectedFiberNumberedCoverClass.pullback_smul`), and it is
characterized by `TauCeti.ConnectedFiberNumberedCoverClass.forgetNumbering_pullback` and
`pullback_mk`. -/
noncomputable def pullback (C : ConnectedCoverClass y n) : ConnectedCoverClass x n :=
  Quotient.lift (s := MulAction.orbitRel (Perm (Fin n)) _)
    (fun N : ConnectedFiberNumberedCoverClass y n => (N.pullback h hx).forgetNumbering)
    (fun _ N' hNN' => by
      obtain ⟨τ, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hNN')
      rw [pullback_smul, forgetNumbering_smul])
    (orbitRelQuotientEquiv.symm C)

end ConnectedCoverClass

/-- Forgetting the numbering commutes with pullback, on classes. -/
@[simp]
theorem ConnectedFiberNumberedCoverClass.forgetNumbering_pullback
    (C : ConnectedFiberNumberedCoverClass y n) :
    (C.pullback h hx).forgetNumbering = C.forgetNumbering.pullback h hx := by
  rw [ConnectedCoverClass.pullback, orbitRelQuotientEquiv_symm_forgetNumbering]
  rfl

/-- The pullback of the class of a bare cover is the class of its pullback. -/
@[simp]
theorem ConnectedCoverClass.pullback_mk (c : ConnectedCover y n) :
    (mk c).pullback h hx = mk (c.pullback h hx) := by
  have hc : mk c = (ConnectedFiberNumberedCoverClass.mk c.numbering).forgetNumbering := by
    rw [ConnectedFiberNumberedCoverClass.forgetNumbering_mk, c.forgetNumbering_numbering]
  rw [hc, ← ConnectedFiberNumberedCoverClass.forgetNumbering_pullback,
    ConnectedFiberNumberedCoverClass.pullback_mk,
    ConnectedFiberNumberedCoverClass.forgetNumbering_mk,
    ConnectedFiberNumberedCover.forgetNumbering_pullback, c.forgetNumbering_numbering]

/-- Forgetting the chosen point commutes with pullback, on classes. -/
@[simp]
theorem ConnectedPointedCoverClass.forgetPoint_pullback (C : ConnectedPointedCoverClass y n) :
    (C.pullback h hx).forgetPoint = C.forgetPoint.pullback h hx := by
  obtain ⟨c, rfl⟩ := ConnectedPointedCoverClass.mk_surjective C
  rw [ConnectedPointedCoverClass.pullback_mk, ConnectedPointedCoverClass.forgetPoint_mk,
    ConnectedPointedCoverClass.forgetPoint_mk, ConnectedCoverClass.pullback_mk,
    ConnectedPointedCover.forgetPoint_pullback]

namespace ConnectedCoverClass

/-- Pulling back along the identity changes nothing, on classes. -/
@[simp]
theorem pullback_refl (C : ConnectedCoverClass x n) :
    C.pullback (Homeomorph.refl X) (y := x) rfl = C := by
  obtain ⟨c, rfl⟩ := mk_surjective C
  exact (pullback_mk _ _ c).trans (congrArg mk (ConnectedCover.pullback_refl c))

/-- Pulling back twice is pulling back along the composite homeomorphism, on classes. -/
@[simp]
theorem pullback_pullback (C : ConnectedCoverClass z n) :
    (C.pullback h' hy).pullback h hx =
      C.pullback (h.trans h') ((h.trans_apply h' x).trans ((congrArg h' hx).trans hy)) := by
  obtain ⟨c, rfl⟩ := mk_surjective C
  rw [pullback_mk, pullback_mk, pullback_mk, ConnectedCover.pullback_pullback]

end ConnectedCoverClass

end TauCeti
