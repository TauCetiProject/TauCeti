/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.AlgebraicGeometry.LineBundle.Stalk
public import TauCeti.AlgebraicGeometry.LineBundle.Power
public import TauCeti.AlgebraicGeometry.Modules.Pullback.ResidueField
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Sections
public import TauCeti.RingTheory.LocalRing.Module
import TauCeti.Algebra.Module.Equiv.SpanSingleton

/-!
# The nonvanishing locus of a section of an invertible sheaf

Let `M` be an invertible sheaf on a scheme `X` and `s` a section of `M` over an open `U`. The
**nonvanishing locus** `X_s` is the set of points `x ∈ U` at which the germ of `s` generates the
stalk `M_x`, equivalently at which `s` does not vanish in the fibre `M_x ⊗ κ(x)`. Over an open `V`
on which `M` is trivialized, `s` is a regular function times the basis section, and `X_s ∩ V` is
the basic open set of that function; in particular `X_s` is open. It generalizes the basic open
set `X_f` of a regular function, the case of the structure sheaf.

These open sets are the ones through which positivity of line bundles is defined: `M` is globally
generated when the sets `X_s` of its global sections cover `X`, and ample when `X` is
quasi-compact and the sets `X_s` that are affine, for global sections `s` of the positive tensor
powers of `M`, cover `X`.

The section `s` is a basis of `M` exactly over its nonvanishing locus: an open `W ⊆ U` lies in
`X_s` if and only if, on every open `W' ⊆ W`, every section of `M` is a unique regular multiple
of the restriction of `s`. In other words, `s` trivializes `M` over `X_s`.

On an affine open `U`, the nonvanishing locus of every section over `U` is affine: over a cover of
`U` by basic opens trivializing `M` it is a basic open of each member. Moreover the sections over
`U` generate every stalk, since the sections over a basic open `D(f) ⊆ U` are the localization at
`f` of the sections over `U`. These are the two facts making every invertible sheaf on an affine
scheme ample.

Pullback of sections commutes with nonvanishing loci for every scheme morphism, and the
nonvanishing locus of a tensor product of sections is the intersection of their loci. Positive
powers of a section retain its nonvanishing locus, in any representative of the tensor-power
class. These operations transport affine nonvanishing neighbourhoods in the study of ampleness.

The pullback, fibre and tensor arguments are adapted from `roed-math/TauCeti-w2-fresh`, branch
`lookahead/StableReduction/relative-ampleness`, commit `efa6fc8f3735`.

For a line bundle `L` whose class in the Picard group is trivial, `L` is only isomorphic to `𝒪_X`,
not equal to it, but the nonvanishing loci of its sections over `U` are still exactly the basic
open sets of the regular functions on `U`. When the global functions on `X` form a field, as on an
integral scheme universally closed over a field (`AlgebraicGeometry.isField_of_universallyClosed`),
a global section of `L` therefore vanishes either everywhere or nowhere.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus`: the open set `X_s` of points at which the
  germ of `s` generates the stalk.

## Main results

* `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_eq_basicOpen`: on the domain of a rank-one
  trivialization, `X_s` is the basic open set of the coordinate of `s`;
* `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_map` and
  `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_smul`: restriction intersects `X_s` with the
  smaller open, and `X_{r s} = X_r ∩ X_s` for a regular function `r`;
* `AlgebraicGeometry.Scheme.Modules.le_nonvanishingLocus_iff`: `s` is a basis of `M` exactly over
  open subsets of `X_s`;
* `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_hom_app`: the nonvanishing locus is
  invariant under isomorphisms of invertible sheaves;
* `AlgebraicGeometry.Scheme.Modules.range_nonvanishingLocus_eq_of_iso`: isomorphic invertible
  sheaves have the same nonvanishing loci of sections over each open;
* `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_unit`: on the structure sheaf, `X_r` is the
  basic open set of the regular function `r`;
* `AlgebraicGeometry.Scheme.Modules.basicOpen_eq_inf_nonvanishingLocus`: if `s|_V = f • e` with
  `e` nonvanishing on `V`, then `X_s ∩ V` is the basic open set of `f`;
* `AlgebraicGeometry.Scheme.Modules.quasiSeparatedSpace_of_forall_isAffineOpen_nonvanishingLocus`:
  a scheme covered by affine nonvanishing loci of global sections of `M` is quasi-separated;
* `AlgebraicGeometry.IsAffineOpen.nonvanishingLocus`: on an affine open, `X_s` is affine;
  `AlgebraicGeometry.IsAffineOpen.inf_nonvanishingLocus`: if `V` is affine and `V ≤ W`,
  then `V ∩ X_t` is affine for a section `t` over `W`;
* `AlgebraicGeometry.Scheme.Modules.exists_mem_nonvanishingLocus_of_isAffineOpen`: every point of
  an affine open `U` lies in `X_s` for some section `s` over `U`;
* `AlgebraicGeometry.Scheme.Hom.nonvanishingLocus_pullbackSections` and
  `AlgebraicGeometry.Scheme.Hom.nonvanishingLocus_restrictAppIso_inv`: the nonvanishing locus
  of a pulled-back or restricted section is the preimage;
* `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_tmulRight` and
  `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_tensorPowSection`: `X_{s ⊗ t} = X_s ∩ X_t`,
  and `X_{sᵏ} = X_s` for `k > 0`;
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.exists_nonvanishingLocus_eq_of_mk_eq_pow`: every
  representative of the class `(mk L₀)ᵏ`, with `k > 0`, has a section with the same
  nonvanishing locus as `s₀`;
* `InvertibleSheaf.range_nonvanishingLocus_eq_range_basicOpen_of_mk_eq_one`:
  the nonvanishing loci of sections of a line bundle of trivial class are the basic open sets;
* `InvertibleSheaf.nonvanishingLocus_eq_bot_or_eq_top_of_isField_of_mk_eq_one`:
  when `Γ(X, ⊤)` is a field, a global section of a line bundle of trivial class vanishes
  everywhere or nowhere.

## References

* The Stacks Project, Tag 01CT (the open `X_s` attached to a section of an invertible sheaf) and
  Tag 01PS (ample invertible sheaves).
* The Stacks Project, *Properties of Schemes*, the section on ample invertible sheaves (around
  Tag 01PS), for the affineness of `X_s` on an affine scheme.
* R. Hartshorne, *Algebraic Geometry*, Chapter II, Section 7.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} (M : X.Modules)
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M]

/-- On the domain of a rank-one trivialization, the germ of a section generates the stalk exactly
when the germ of its coordinate is a unit of the local ring. -/
theorem span_germ_eq_top_iff_isUnit {V W : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) (i : W ⟶ V)
    (s : Γ(M, W)) {x : X} (hx : x ∈ W) :
    Submodule.span (X.presheaf.stalk x) {M.presheaf.germ W x hx s} = ⊤ ↔
      IsUnit (X.presheaf.germ W x hx (trivializationCoordinate M t i s)) := by
  conv_lhs => rw [eq_trivializationCoordinate_smul_map_trivializationGenerator M t i s]
  rw [germ_smul, TopCat.Presheaf.germ_res_apply, span_smul_eq_top_iff,
    span_germ_trivializationGenerator M x t (i.le hx)]
  exact and_iff_left rfl

/-- The **nonvanishing locus** `X_s` of a section `s` of an invertible sheaf over `U`: the open
set of points of `U` at which the germ of `s` generates the stalk. -/
def nonvanishingLocus {U : X.Opens} (s : Γ(M, U)) : X.Opens where
  carrier := {x | ∃ hx : x ∈ U,
    Submodule.span (X.presheaf.stalk x) {M.presheaf.germ U x hx s} = ⊤}
  is_open' := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨hxU, hx⟩
    obtain ⟨V, t, hxV⟩ := exists_mem_trivialization M x
    let i : U ⊓ V ⟶ V := homOfLE inf_le_right
    let j : U ⊓ V ⟶ U := homOfLE inf_le_left
    -- Near `x`, the locus contains the basic open set of the coordinate of `s`.
    have key {y : X} (hy : y ∈ U ⊓ V) :
        Submodule.span (X.presheaf.stalk y) {M.presheaf.germ U y (j.le hy) s} = ⊤ ↔
          y ∈ X.basicOpen (trivializationCoordinate M t i (M.presheaf.map j.op s)) := by
      rw [X.mem_basicOpen _ _ hy, ← span_germ_eq_top_iff_isUnit M t i _ hy,
        TopCat.Presheaf.germ_res_apply]
    exact ⟨_, fun y hy ↦ ⟨_, (key (X.basicOpen_le _ hy)).mpr hy⟩, (X.basicOpen _).isOpen,
      (key ⟨hxU, hxV⟩).mp hx⟩

variable {M}

/-- A point lies in the nonvanishing locus of `s` exactly when it lies in the domain of `s` and the
germ of `s` there generates the stalk. -/
theorem mem_nonvanishingLocus_iff {U : X.Opens} {s : Γ(M, U)} {x : X} :
    x ∈ M.nonvanishingLocus s ↔
      ∃ hx : x ∈ U, Submodule.span (X.presheaf.stalk x) {M.presheaf.germ U x hx s} = ⊤ :=
  Iff.rfl

/-- A point of the domain of `s` lies in its nonvanishing locus exactly when the germ of `s`
generates the stalk there. -/
theorem mem_nonvanishingLocus_iff_of_mem {U : X.Opens} {s : Γ(M, U)} {x : X} (hx : x ∈ U) :
    x ∈ M.nonvanishingLocus s ↔
      Submodule.span (X.presheaf.stalk x) {M.presheaf.germ U x hx s} = ⊤ :=
  ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hx, h⟩⟩

/-- The nonvanishing locus of a section over `U` is contained in `U`. -/
theorem nonvanishingLocus_le {U : X.Opens} (s : Γ(M, U)) : M.nonvanishingLocus s ≤ U :=
  fun _ ⟨hx, _⟩ ↦ hx

/-- On the domain of a rank-one trivialization, the nonvanishing locus of a section is the basic
open set of its coordinate. -/
theorem nonvanishingLocus_eq_basicOpen {U V : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) (i : U ⟶ V)
    (s : Γ(M, U)) :
    M.nonvanishingLocus s = X.basicOpen (trivializationCoordinate M t i s) := by
  ext x
  refine ⟨fun ⟨hx, h⟩ ↦ ?_, fun h ↦ ?_⟩
  · exact (X.mem_basicOpen _ _ hx).mpr ((span_germ_eq_top_iff_isUnit M t i s hx).mp h)
  · have hx := X.basicOpen_le _ h
    exact ⟨hx, (span_germ_eq_top_iff_isUnit M t i s hx).mpr ((X.mem_basicOpen _ _ hx).mp h)⟩

/-- The nonvanishing locus of a restricted section is the intersection of the smaller open with
the nonvanishing locus of the section. -/
@[simp]
theorem nonvanishingLocus_map {U W : X.Opens} (j : W ⟶ U) (s : Γ(M, U)) :
    M.nonvanishingLocus (M.presheaf.map j.op s) = W ⊓ M.nonvanishingLocus s := by
  ext x
  refine ⟨fun ⟨hx, h⟩ ↦ ⟨hx, j.le hx, ?_⟩, fun ⟨hx, _, h⟩ ↦ ⟨hx, ?_⟩⟩
  · rwa [TopCat.Presheaf.germ_res_apply] at h
  · rwa [TopCat.Presheaf.germ_res_apply]

/-- The nonvanishing locus of a regular multiple `r • s` is the intersection of the basic open set
of `r` with the nonvanishing locus of `s`. -/
@[simp]
theorem nonvanishingLocus_smul {U : X.Opens} (r : Γ(X, U)) (s : Γ(M, U)) :
    M.nonvanishingLocus (r • s) = X.basicOpen r ⊓ M.nonvanishingLocus s := by
  ext x
  refine ⟨fun ⟨hx, h⟩ ↦ ?_, fun ⟨hr, hx, h⟩ ↦ ⟨hx, ?_⟩⟩
  · rw [germ_smul, span_smul_eq_top_iff] at h
    exact ⟨(X.mem_basicOpen _ _ hx).mpr h.1, hx, h.2⟩
  · rw [germ_smul, span_smul_eq_top_iff]
    exact ⟨(X.mem_basicOpen _ _ hx).mp hr, h⟩

/-- The zero section vanishes everywhere. -/
@[simp]
theorem nonvanishingLocus_zero (U : X.Opens) : M.nonvanishingLocus (0 : Γ(M, U)) = ⊥ := by
  rw [← zero_smul Γ(X, U) (0 : Γ(M, U)), nonvanishingLocus_smul, X.basicOpen_zero, bot_inf_eq]

/-- The basis section of a rank-one trivialization over `V` vanishes nowhere on `V`. -/
@[simp]
theorem nonvanishingLocus_trivializationGenerator {V : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) :
    M.nonvanishingLocus (trivializationGenerator M t) = V := by
  rw [nonvanishingLocus_eq_basicOpen t (𝟙 V), trivializationCoordinate_trivializationGenerator,
    X.basicOpen_one]

/-- A section is a nonzerodivisor for the regular functions over any open contained in its
nonvanishing locus. -/
theorem injective_smul_of_le_nonvanishingLocus {U : X.Opens} {s : Γ(M, U)}
    (h : U ≤ M.nonvanishingLocus s) : Function.Injective fun r : Γ(X, U) ↦ r • s := by
  intro r r' hrr'
  refine TopCat.Presheaf.section_ext X.sheaf U r r' fun x hx ↦ ?_
  have hs := (mem_nonvanishingLocus_iff_of_mem hx).mp (h hx)
  refine (bijective_toSpanSingleton_of_span_eq_top M x hs).1 ?_
  have hgerm := congrArg (M.presheaf.germ U x hx) hrr'
  simp only [germ_smul] at hgerm
  exact hgerm

/-- Every section over an open contained in the nonvanishing locus of `s` is a regular multiple
of `s`. -/
theorem surjective_smul_of_le_nonvanishingLocus {U : X.Opens} {s : Γ(M, U)}
    (h : U ≤ M.nonvanishingLocus s) : Function.Surjective fun r : Γ(X, U) ↦ r • s := by
  intro m
  -- Near each point `x` of `U`, the germ of `m` is a multiple of the germ of `s`, so `m` is a
  -- multiple `r x • s` on a neighbourhood `N x ⊆ U` of `x`.
  have hloc (x : U) : ∃ (N : X.Opens) (_ : (x : X) ∈ N) (k : N ⟶ U) (r : Γ(X, N)),
      r • M.presheaf.map k.op s = M.presheaf.map k.op m := by
    have hs := (mem_nonvanishingLocus_iff_of_mem x.property).mp (h x.property)
    obtain ⟨a, ha⟩ := (Submodule.span_singleton_eq_top_iff _ _).mp hs
        (M.presheaf.germ U x x.property m)
    obtain ⟨W, hxW, r, rfl⟩ := X.presheaf.exists_germ_eq a
    let p : W ⊓ U ⟶ W := homOfLE inf_le_left
    let q : W ⊓ U ⟶ U := homOfLE inf_le_right
    have hxWU : (x : X) ∈ W ⊓ U := ⟨hxW, x.property⟩
    have ha' : M.presheaf.germ (W ⊓ U) x hxWU
        (X.presheaf.map p.op r • M.presheaf.map q.op s) =
          M.presheaf.germ (W ⊓ U) x hxWU (M.presheaf.map q.op m) := by
      rw [germ_smul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
        TopCat.Presheaf.germ_res_apply]
      exact ha
    obtain ⟨N, hxN, k, k', hk⟩ := M.presheaf.germ_eq _ hxWU hxWU _ _ ha'
    rw [Subsingleton.elim k' k] at hk
    refine ⟨N, hxN, k ≫ q, X.presheaf.map (k ≫ p).op r, ?_⟩
    simpa only [map_smul, op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using hk
  choose N hxN k r hr using hloc
  have hcover : U ≤ iSup N := fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxN ⟨x, hx⟩⟩
  -- The local coefficients agree on overlaps, because `s` is a nonzerodivisor there.
  have hres {x : U} {O : X.Opens} (j : O ⟶ N x) (a : O ⟶ U) :
      X.presheaf.map j.op (r x) • M.presheaf.map a.op s = M.presheaf.map a.op m := by
    obtain rfl : a = j ≫ k x := Subsingleton.elim _ _
    have hx := congrArg (M.presheaf.map j.op) (hr x)
    simpa only [map_smul, op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using hx
  obtain ⟨c, hc, -⟩ : ∃! c : Γ(X, U), ∀ x, X.presheaf.map (k x).op c = r x :=
    X.sheaf.existsUnique_gluing' N U k hcover r fun x y ↦ by
      let a : N x ⊓ N y ⟶ U := Opens.infLELeft _ _ ≫ k x
      have ha : N x ⊓ N y ≤ M.nonvanishingLocus (M.presheaf.map a.op s) := by
        rw [nonvanishingLocus_map]
        exact le_inf le_rfl (a.le.trans h)
      exact injective_smul_of_le_nonvanishingLocus ha
        ((hres _ a).trans (hres (Opens.infLERight _ _) a).symm)
  -- The glued coefficient works, since both sides have the same germ at every point of `U`.
  refine ⟨c, TopCat.Presheaf.section_ext (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    U _ _ fun x hx ↦ ?_⟩
  rw [← TopCat.Presheaf.germ_res_apply M.presheaf (k ⟨x, hx⟩) _ (hxN ⟨x, hx⟩),
    ← TopCat.Presheaf.germ_res_apply M.presheaf (k ⟨x, hx⟩) _ (hxN ⟨x, hx⟩)]
  exact congrArg _ ((map_smul M _ c s).trans
    ((congrArg (· • _) (hc ⟨x, hx⟩)).trans (hr ⟨x, hx⟩)))

/-- **A section is a basis exactly over its nonvanishing locus.** An open `W ⊆ U` lies in the
nonvanishing locus of `s` if and only if, on every open `W' ⊆ W`, every section of `M` is a unique
regular multiple of the restriction of `s`. -/
theorem le_nonvanishingLocus_iff {U W : X.Opens} (s : Γ(M, U)) (i : W ⟶ U) :
    W ≤ M.nonvanishingLocus s ↔ ∀ (W' : X.Opens) (j : W' ⟶ W),
      Function.Bijective fun r : Γ(X, W') ↦ r • M.presheaf.map (j ≫ i).op s := by
  refine ⟨fun h W' j ↦ ?_, fun h x hxW ↦ ⟨i.le hxW, ?_⟩⟩
  · have h' : W' ≤ M.nonvanishingLocus (M.presheaf.map (j ≫ i).op s) := by
      rw [nonvanishingLocus_map]
      exact le_inf le_rfl (j.le.trans h)
    exact ⟨injective_smul_of_le_nonvanishingLocus h', surjective_smul_of_le_nonvanishingLocus h'⟩
  · -- Every germ of `M` at `x` is the germ of a section over an open `W' ⊆ W`, which is a multiple
    -- of the restriction of `s`.
    refine (Submodule.span_singleton_eq_top_iff _ _).mpr fun m ↦ ?_
    obtain ⟨W'', hxW'', m, rfl⟩ := M.presheaf.exists_germ_eq m
    let j : W'' ⊓ W ⟶ W := homOfLE inf_le_right
    let k : W'' ⊓ W ⟶ W'' := homOfLE inf_le_left
    have hx : x ∈ W'' ⊓ W := ⟨hxW'', hxW⟩
    obtain ⟨r, hr⟩ := (h _ j).2 (M.presheaf.map k.op m)
    beta_reduce at hr
    refine ⟨X.presheaf.germ _ x hx r, ?_⟩
    rw [← TopCat.Presheaf.germ_res_apply M.presheaf (j ≫ i) _ hx, ← germ_smul, hr,
      TopCat.Presheaf.germ_res_apply]

/-- The nonvanishing locus is invariant under isomorphisms of invertible sheaves. -/
@[simp]
theorem nonvanishingLocus_hom_app {N : X.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X N] (φ : M ≅ N) {U : X.Opens}
    (s : Γ(M, U)) :
    N.nonvanishingLocus (φ.hom.app U s) = M.nonvanishingLocus s := by
  have hnat {W W' : X.Opens} (j : W' ⟶ W) (y : Γ(M, W)) :
      φ.hom.app W' (M.presheaf.map j.op y) = N.presheaf.map j.op (φ.hom.app W y) := by
    simpa only [mapPresheaf_app, unop_op] using φ.hom.mapPresheaf.naturality_apply j.op y
  -- Multiplication by the image of `s` is multiplication by `s` followed by the bijection `φ`.
  have hbij {W' : X.Opens} (i : W' ⟶ U) :
      (Function.Bijective fun r : Γ(X, W') ↦ r • N.presheaf.map i.op (φ.hom.app U s)) ↔
        Function.Bijective fun r : Γ(X, W') ↦ r • M.presheaf.map i.op s := by
    have hφ : Function.Bijective (φ.hom.app W') :=
      (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
    have heq : (fun r : Γ(X, W') ↦ r • N.presheaf.map i.op (φ.hom.app U s)) =
        φ.hom.app W' ∘ fun r : Γ(X, W') ↦ r • M.presheaf.map i.op s := by
      ext r
      simp [hnat]
    rw [heq, Function.Bijective.of_comp_iff' hφ]
  refine le_antisymm ?_ ?_
  · refine (le_nonvanishingLocus_iff s (homOfLE (nonvanishingLocus_le _))).mpr fun W' j ↦ ?_
    rw [← hbij]
    exact (le_nonvanishingLocus_iff _ (homOfLE (nonvanishingLocus_le _))).mp le_rfl W' j
  · refine (le_nonvanishingLocus_iff _ (homOfLE (nonvanishingLocus_le _))).mpr fun W' j ↦ ?_
    rw [hbij]
    exact (le_nonvanishingLocus_iff s (homOfLE (nonvanishingLocus_le _))).mp le_rfl W' j

/-- Isomorphic invertible sheaves have the same nonvanishing loci of sections over `U`: the set of
opens `X_s`, for `s` a section over `U`, is invariant under isomorphism. -/
theorem range_nonvanishingLocus_eq_of_iso {N : X.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X N] (φ : M ≅ N) (U : X.Opens) :
    Set.range (M.nonvanishingLocus (U := U)) = Set.range (N.nonvanishingLocus (U := U)) := by
  ext V
  exact ⟨fun ⟨s, hs⟩ ↦ ⟨φ.hom.app U s, (nonvanishingLocus_hom_app φ s).trans hs⟩,
    fun ⟨s, hs⟩ ↦ ⟨φ.symm.hom.app U s, (nonvanishingLocus_hom_app φ.symm s).trans hs⟩⟩

/-- If `e` vanishes nowhere on `V ≤ U` and `s|_V = f • e`, then `X_s ∩ V` is the basic open set
of `f`. -/
theorem basicOpen_eq_inf_nonvanishingLocus {U V : X.Opens} (i : V ⟶ U) (s : Γ(M, U))
    {e : Γ(M, V)} (he : V ≤ M.nonvanishingLocus e) {f : Γ(X, V)}
    (hf : f • e = M.presheaf.map i.op s) : X.basicOpen f = V ⊓ M.nonvanishingLocus s := by
  rw [← inf_eq_left.mpr ((X.basicOpen_le f).trans he), ← nonvanishingLocus_smul, hf,
    nonvanishingLocus_map]

/-- A scheme covered by affine nonvanishing loci of global sections of an invertible sheaf is
quasi-separated: two such loci `X_s` and `X_t` meet in the basic open of `X_s` cut out by the
function `t / s`, which is affine. -/
theorem quasiSeparatedSpace_of_forall_isAffineOpen_nonvanishingLocus
    (h : ∀ x : X, ∃ s : Γ(M, ⊤), x ∈ M.nonvanishingLocus s ∧
      IsAffineOpen (M.nonvanishingLocus s)) :
    QuasiSeparatedSpace X := by
  let S := {s : Γ(M, ⊤) // IsAffineOpen (M.nonvanishingLocus s)}
  refine Scheme.quasiSeparatedSpace_of_isOpenCover (fun s : S ↦ M.nonvanishingLocus s.val)
    (top_unique fun x _ ↦ ?_) (fun s ↦ s.property) fun s t ↦ ?_
  · obtain ⟨s, hxs, hs⟩ := h x
    exact Opens.mem_iSup.mpr ⟨⟨s, hs⟩, hxs⟩
  -- On `X_s`, write `t = g • s`; then `X_s ∩ X_t` is the basic open of `g` in `X_s`.
  let j : M.nonvanishingLocus s.val ⟶ ⊤ := homOfLE le_top
  have hss : M.nonvanishingLocus s.val ≤ M.nonvanishingLocus (M.presheaf.map j.op s.val) := by
    rw [nonvanishingLocus_map]
    exact le_inf le_rfl le_rfl
  obtain ⟨g, hg⟩ := surjective_smul_of_le_nonvanishingLocus hss (M.presheaf.map j.op t.val)
  rw [← Opens.coe_inf, ← basicOpen_eq_inf_nonvanishingLocus j t.val hss hg]
  exact (s.property.basicOpen g).isCompact

/-- On the structure sheaf `𝒪_X`, regarded as an invertible sheaf, the nonvanishing locus of a
regular function `r` is its basic open set `X_r`. -/
@[simp]
theorem nonvanishingLocus_unit {U : X.Opens} (r : Γ(X, U)) :
    nonvanishingLocus (SheafOfModules.unit X.ringCatSheaf)
      (show Γ(SheafOfModules.unit X.ringCatSheaf, U) from r) = X.basicOpen r := by
  -- The sections of `𝒪_X` over an open `W` are, by definition, the regular functions on `W`,
  -- on which `Γ(X, W)` acts by multiplication and restriction is restriction of functions;
  -- the `show` in the statement and the term `h a` below use this identification.
  let one : Γ(SheafOfModules.unit X.ringCatSheaf, U) := (1 : Γ(X, U))
  have hone : nonvanishingLocus (SheafOfModules.unit X.ringCatSheaf) one = U := by
    refine le_antisymm (nonvanishingLocus_le one) ((le_nonvanishingLocus_iff one (𝟙 U)).mpr ?_)
    intro W j
    have h (a : Γ(X, W)) : a * X.presheaf.map (j ≫ 𝟙 U).op 1 = a := by rw [map_one, mul_one]
    exact ⟨fun a b hab ↦ (h a).symm.trans (hab.trans (h b)), fun a ↦ ⟨a, h a⟩⟩
  convert nonvanishingLocus_smul (M := SheafOfModules.unit X.ringCatSheaf) r one using 1
  · exact congrArg _ (mul_one r).symm
  · rw [hone]
    exact (inf_eq_left.mpr (X.basicOpen_le r)).symm

/-- **Nonvanishing loci in an affine open are affine.** If `U` is an affine open of `X`, then the
nonvanishing locus `X_s` of every section `s` of an invertible sheaf over `U` is affine. -/
theorem _root_.AlgebraicGeometry.IsAffineOpen.nonvanishingLocus {U : X.Opens}
    (hU : IsAffineOpen U) (s : Γ(M, U)) : IsAffineOpen (M.nonvanishingLocus s) := by
  -- Cover `U` by basic opens `D(f)` on which `M` is trivial; on each of them `X_s` is the basic
  -- open of the coordinate of `s`, so affine.
  have H (x : U) : ∃ f : Γ(X, U), (x : X) ∈ X.basicOpen f ∧
      IsAffineOpen (M.nonvanishingLocus s ⊓ X.basicOpen f) := by
    obtain ⟨V, t, hxV⟩ := exists_mem_trivialization M x
    obtain ⟨f, hfV, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ x.property
    refine ⟨f, hxf, ?_⟩
    rw [inf_comm, ← nonvanishingLocus_map (homOfLE (X.basicOpen_le f)),
      nonvanishingLocus_eq_basicOpen t (homOfLE hfV)]
    exact (hU.basicOpen f).basicOpen _
  choose f hxf hf using H
  -- The restrictions of the functions `f` to `X_s` generate the unit ideal, and their basic opens
  -- are the affine opens `X_s ∩ D(f)`.
  let j : M.nonvanishingLocus s ⟶ U := homOfLE (M.nonvanishingLocus_le s)
  refine isAffineOpen_of_isAffineOpen_basicOpen _ (X.presheaf.map j.op '' Set.range f) ?_ ?_
  · rw [← Ideal.map_span, (hU.self_le_iSup_basicOpen_iff (s := Set.range f)).mp, Ideal.map_top]
    exact fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨f ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩, hxf ⟨x, hx⟩⟩
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    rw [X.basicOpen_res]
    exact hf x

/-- The intersection of an affine open `V ≤ W` with the nonvanishing locus of a section over `W` is
affine: it is the nonvanishing locus of the restriction of the section to `V`. -/
theorem _root_.AlgebraicGeometry.IsAffineOpen.inf_nonvanishingLocus {V W : X.Opens}
    (hV : IsAffineOpen V) (hVW : V ≤ W) (t : Γ(M, W)) :
    IsAffineOpen (V ⊓ M.nonvanishingLocus t) := by
  rw [← nonvanishingLocus_map (homOfLE hVW) t]
  exact hV.nonvanishingLocus _

variable (M) in
/-- **Sections over an affine open generate the stalks.** Every point `x` of an affine open `U`
lies in the nonvanishing locus of some section of an invertible sheaf over `U`. -/
theorem exists_mem_nonvanishingLocus_of_isAffineOpen {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U) : ∃ s : Γ(M, U), x ∈ M.nonvanishingLocus s := by
  have : M.IsQuasicoherent :=
    TauCeti.AlgebraicGeometry.InvertibleSheaf.isQuasicoherent_obj ⟨M, ‹_›⟩
  obtain ⟨V, t, hxV⟩ := exists_mem_trivialization M x
  obtain ⟨f, hfV, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hx
  -- A power of `f` times the basis section over `D(f) ⊆ V` extends to a section `s` over `U`,
  -- so `s` vanishes nowhere on `D(f)`.
  obtain ⟨n, s, hs⟩ := M.exists_pow_smul_eq_map hU f rfl (X.basicOpen_le f)
    (M.presheaf.map (homOfLE hfV).op (trivializationGenerator M t))
  refine ⟨s, (inf_le_right : X.basicOpen f ⊓ _ ≤ _) ?_⟩
  rw [← nonvanishingLocus_map (homOfLE (X.basicOpen_le f)), ← hs,
    nonvanishingLocus_smul, nonvanishingLocus_map,
    nonvanishingLocus_trivializationGenerator, ← map_pow, X.basicOpen_res]
  refine ⟨⟨hxf, ?_⟩, hxf, hxV⟩
  rw [SetLike.mem_coe, X.mem_basicOpen _ _ hx, map_pow]
  exact ((X.mem_basicOpen _ _ hx).mp hxf).pow n

section Pullback

/-- **A section vanishes nowhere exactly where it is nonzero in the fibre.** A point `x` of `U`
lies in the nonvanishing locus of a section `s` over `U` exactly when the pullback of `s` along
`Spec κ(x) ⟶ X`, an element of the fibre `κ(x) ⊗ M_x`, is nonzero. -/
theorem mem_nonvanishingLocus_iff_pullbackSectionsLE_ne_zero {U : X.Opens} (s : Γ(M, U)) {x : X}
    (hx : x ∈ U) :
    x ∈ M.nonvanishingLocus s ↔ Scheme.Hom.pullbackSectionsLE (X.fromSpecResidueField x) M U ⊤
      (fromSpecResidueField_preimage_eq_top x hx).ge s ≠ 0 := by
  have : M.IsQuasicoherent :=
    TauCeti.AlgebraicGeometry.InvertibleSheaf.isQuasicoherent_obj ⟨M, ‹_›⟩
  have := Module.finite_of_finrank_eq_succ (finrank_stalk_of_isInvertible M x)
  rw [mem_nonvanishingLocus_iff_of_mem hx,
    TauCeti.IsLocalRing.span_singleton_eq_top_iff_one_tmul_ne_zero
      (Module.finrank_baseChange.trans (finrank_stalk_of_isInvertible M x)),
    ← one_smul (X.residueField x) (Scheme.Hom.pullbackSectionsLE _ M U ⊤ _ s),
    ← residueFieldPullbackSectionsEquiv_tmul_germ x M hx, LinearEquiv.map_ne_zero_iff]
  -- The two sides differ only in their residue field: `X.residueField x` is defined as the
  -- bundled `IsLocalRing.ResidueField (X.presheaf.stalk x)`, with its field and algebra structures
  -- inherited from it, and Mathlib has no lemma rewriting one into the other.
  rfl

/-- **The nonvanishing locus of a pulled-back section is the preimage.** For a morphism
`g : Y ⟶ X` and a section `s` of the invertible sheaf `M` over `U`, the pullback of `s` to a
section of `g^* M` over `g⁻¹ U` has nonvanishing locus `g⁻¹ X_s`. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Hom.nonvanishingLocus_pullbackSections
    {Y : Scheme.{u}} (g : Y ⟶ X) {U : X.Opens} (s : Γ(M, U)) :
    ((pullback g).obj M).nonvanishingLocus (g.pullbackSections M U s) =
      g ⁻¹ᵁ M.nonvanishingLocus s := by
  ext y
  simp only [SetLike.mem_coe, Scheme.Hom.mem_preimage]
  by_cases hy : g y ∈ U
  swap
  · exact iff_of_false
      (fun h ↦ hy ((g.mem_preimage (U := U) (x := y)).mp (nonvanishingLocus_le _ h)))
      (fun h ↦ hy (nonvanishingLocus_le _ h))
  have hyU : y ∈ g ⁻¹ᵁ U := (g.mem_preimage (U := U) (x := y)).mpr hy
  rw [mem_nonvanishingLocus_iff_pullbackSectionsLE_ne_zero _ hyU,
    mem_nonvanishingLocus_iff_pullbackSectionsLE_ne_zero _ hy]
  let p := Y.fromSpecResidueField y
  let q := X.fromSpecResidueField (g y)
  let f := Spec.map (g.residueFieldMap y)
  have hp : ⊤ ≤ p ⁻¹ᵁ (g ⁻¹ᵁ U) :=
    (fromSpecResidueField_preimage_eq_top y hyU).ge
  have hq : ⊤ ≤ q ⁻¹ᵁ U := (fromSpecResidueField_preimage_eq_top (g y) hy).ge
  have hW : (⊤ : (Spec (Y.residueField y)).Opens) ≤ f ⁻¹ᵁ ⊤ := le_rfl
  have hc : p ≫ g = f ≫ q :=
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g y).symm
  let e := (pullbackComp p g).app M ≪≫ (pullbackCongr hc).app M ≪≫
    ((pullbackComp f q).app M).symm
  -- Compare the two routes from the original section to its value over `κ(y)`.
  have he : e.hom.app ⊤ (p.pullbackSectionsLE _ (g ⁻¹ᵁ U) ⊤ hp
      (g.pullbackSections M U s)) =
      f.pullbackSectionsLE _ ⊤ ⊤ hW (q.pullbackSectionsLE M U ⊤ hq s) := by
    calc
      _ = ((pullbackComp f q).inv.app M).app ⊤
          (((pullbackCongr hc).hom.app M).app ⊤
            ((p ≫ g).pullbackSectionsLE M U ⊤ (hp.trans (Set.preimage_mono le_rfl)) s)) := by
        dsimp only [e, Iso.trans_hom, Iso.symm_hom]
        simp only [Hom.comp_app, ConcreteCategory.comp_apply, Iso.app_hom, Iso.app_inv]
        have h := g.pullbackSectionsLE_comp_hom M U p (g ⁻¹ᵁ U) le_rfl hp s
        rw [g.pullbackSectionsLE_self M U s] at h
        exact congrArg (fun z ↦ ((pullbackComp f q).inv.app M).app ⊤
          (((pullbackCongr hc).hom.app M).app ⊤ z)) h
      _ = ((pullbackComp f q).inv.app M).app ⊤
          ((f ≫ q).pullbackSectionsLE M U ⊤ (hW.trans (Set.preimage_mono hq)) s) := by
        rw [Scheme.Hom.pullbackSectionsLE_congr]
      _ = _ := Scheme.Hom.pullbackSectionsLE_comp q M U f ⊤ hq hW s
  have hi : IsIso (homOfLE hW) :=
    homOfLE_isIso_of_eq _ (Scheme.Hom.preimage_top f).symm
  refine (map_ne_zero_iff (e.hom.app ⊤).hom
    (ConcreteCategory.bijective_of_isIso _).injective).symm.trans ?_
  rw [he]
  exact map_ne_zero_iff _ (f.pullbackSectionsLE_injective_of_isIso _ ⊤ ⊤ hW
    (f.pullbackSections_injective_of_field _))

/-- The nonvanishing locus of a pulled-back section restricted to `V` is the intersection
of `V` with the preimage of the original nonvanishing locus. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Hom.nonvanishingLocus_pullbackSectionsLE
    {Y : Scheme.{u}} (g : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (hV : V ≤ g ⁻¹ᵁ U)
    (s : Γ(M, U)) :
    ((pullback g).obj M).nonvanishingLocus (g.pullbackSectionsLE M U V hV s) =
      V ⊓ g ⁻¹ᵁ M.nonvanishingLocus s := by
  rw [Scheme.Hom.pullbackSectionsLE_apply, nonvanishingLocus_map,
    Scheme.Hom.nonvanishingLocus_pullbackSections]

end Pullback

section Restrict

variable {Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y M]

/-- **The nonvanishing locus of a restricted section is the preimage.** Along an open immersion
`f : X ⟶ Y`, a section `s` of `M` over `f(U)` restricts to a section of `M|_X` over `U`, whose
nonvanishing locus is `f⁻¹ Y_s`. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Hom.nonvanishingLocus_restrictAppIso_inv
    {U : X.Opens} (s : Γ(M, f ''ᵁ U)) :
    (M.restrict f).nonvanishingLocus ((M.restrictAppIso f U).inv s) =
      f ⁻¹ᵁ M.nonvanishingLocus s := by
  -- Under `M|_X ≅ f^* M`, the restricted section is the pullback of `s`, restricted to `U`.
  rw [← nonvanishingLocus_hom_app ((restrictFunctorIsoPullback f).app M), Iso.app_hom,
    restrictFunctorIsoPullback_hom_app_restrictAppIso_inv, Scheme.Hom.pullbackSectionsLE_apply,
    nonvanishingLocus_map, Scheme.Hom.nonvanishingLocus_pullbackSections]
  exact inf_eq_right.mpr ((Scheme.Hom.preimage_mono _ (nonvanishingLocus_le s)).trans
    (f.preimage_image_eq U).le)

end Restrict

section TensorProduct

variable {M N : X.Modules}

/-- **A tensor product of sections vanishes nowhere exactly on the intersection.** For invertible
sheaves `M` and `N` and sections `s` of `M` and `t` of `N` over the same open `U`, the section
`s ⊗ t` of `M ⊗ N` over `U` has nonvanishing locus `X_s ∩ X_t`. -/
@[simp]
theorem nonvanishingLocus_tmulRight
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M]
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X N]
    {U : X.Opens} (s : Γ(M, U)) (t : Γ(N, U)) :
    (M ⊗ N).nonvanishingLocus (tmulRight M t s) =
      M.nonvanishingLocus s ⊓ N.nonvanishingLocus t := by
  ext x
  by_cases hx : x ∈ U
  swap
  · exact iff_of_false (fun h ↦ hx (nonvanishingLocus_le _ h))
      (fun h ↦ hx (nonvanishingLocus_le _ h.1))
  -- At `x` the stalks of `M` and `N` are free of rank one, and the germ of `s ⊗ t` is `s_x ⊗ t_x`.
  obtain ⟨eM⟩ := nonempty_linearEquiv_stalk_of_isInvertible M x
  obtain ⟨eN⟩ := nonempty_linearEquiv_stalk_of_isInvertible N x
  rw [SetLike.mem_coe, SetLike.mem_coe, Opens.mem_inf,
    mem_nonvanishingLocus_iff_of_mem (M := M ⊗ N) hx,
    mem_nonvanishingLocus_iff_of_mem (M := M) hx, mem_nonvanishingLocus_iff_of_mem (M := N) hx,
    ← eM.symm.span_singleton_tmul_eq_top_iff eN.symm, ← tensorStalkEquiv_germ_tmulRight M s t hx]
  exact (M.tensorStalkEquiv N x).span_singleton_apply_eq_top_iff.symm

end TensorProduct

section TensorPow

/-- **Positive powers of a section vanish nowhere exactly where the section does.** For a section
`s` of the invertible sheaf `M` over `U` and `k > 0`, the tensor power `sᵏ`, a section of the
`k`-th tensor power of `M`, has the same nonvanishing locus as `s`. -/
@[simp]
theorem nonvanishingLocus_tensorPowSection {U : X.Opens} (s : Γ(M, U)) {k : ℕ} (hk : 0 < k) :
    (TauCeti.tensorPow M k).nonvanishingLocus (tensorPowSection s k) = M.nonvanishingLocus s := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hk
  rw [zero_add]
  induction n with
  | zero =>
    rw [tensorPowSection_succ, tensorPowSection_zero, ← rightUnitor_inv_app_eq_tmulRight]
    exact nonvanishingLocus_hom_app (ρ_ M).symm s
  | succ n ih =>
    rw [tensorPowSection_succ, nonvanishingLocus_tmulRight, ih (Nat.succ_pos _), inf_idem]

end TensorPow

end AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

open LineBundleClass

variable {X : Scheme.{u}}

/-- **Powers of a section.** A section `s₀` of a line bundle `L₀` gives, in every line bundle
`L` of class `(mk L₀)ᵏ` with `k > 0`, a section with the same nonvanishing locus: the
`k`-fold tensor product `s₀ ⊗ ⋯ ⊗ s₀`, transported along an isomorphism. -/
theorem exists_nonvanishingLocus_eq_of_mk_eq_pow
    {L₀ L : InvertibleSheaf X} {k : ℕ} {U : X.Opens} (hk : 0 < k) (hL : mk L = mk L₀ ^ k)
    (s₀ : Γ(L₀.obj, U)) :
    ∃ s : Γ(L.obj, U), L.obj.nonvanishingLocus s = L₀.obj.nonvanishingLocus s₀ := by
  -- `L` is isomorphic to the monoidal tensor power `L₀^{⊗k}`, whose class is `(mk L₀)ᵏ`.
  have hclass : mk L = mk (TauCeti.tensorPow L₀ k) := by rw [mk_tensorPow, hL]
  obtain ⟨e⟩ := mk_eq_mk_iff.mp hclass
  let e' : L.obj ≅ TauCeti.tensorPow L₀.obj k := e ≪≫ eqToIso (tensorPow_obj L₀ k)
  refine ⟨e'.inv.app U (Scheme.Modules.tensorPowSection s₀ k), ?_⟩
  rw [← Iso.symm_hom, Scheme.Modules.nonvanishingLocus_hom_app,
    Scheme.Modules.nonvanishingLocus_tensorPowSection _ hk]

/-- The nonvanishing loci of the sections over `U` of a line bundle of trivial class are exactly the
basic open sets of the regular functions on `U`. -/
theorem range_nonvanishingLocus_eq_range_basicOpen_of_mk_eq_one {L : InvertibleSheaf X}
    (hL : LineBundleClass.mk L = 1) (U : X.Opens) :
    Set.range (L.obj.nonvanishingLocus (U := U)) = Set.range (X.basicOpen (U := U)) := by
  -- The tensor unit `𝟙_ X.Modules` is by definition the structure sheaf `SheafOfModules.unit`.
  obtain ⟨e⟩ : Nonempty (L.obj ≅ SheafOfModules.unit X.ringCatSheaf) :=
    LineBundleClass.mk_eq_one_iff.mp hL
  rw [Scheme.Modules.range_nonvanishingLocus_eq_of_iso e U]
  exact congrArg Set.range (funext Scheme.Modules.nonvanishingLocus_unit)

/-- When the global functions on `X` form a field, for instance on an integral scheme universally
closed over a field, a global section of a line bundle of trivial class vanishes either everywhere
or nowhere. -/
theorem nonvanishingLocus_eq_bot_or_eq_top_of_isField_of_mk_eq_one (hX : IsField Γ(X, ⊤))
    {L : InvertibleSheaf X} (hL : LineBundleClass.mk L = 1) (s : Γ(L.obj, ⊤)) :
    L.obj.nonvanishingLocus s = ⊥ ∨ L.obj.nonvanishingLocus s = ⊤ := by
  obtain ⟨r, hr⟩ : L.obj.nonvanishingLocus s ∈ Set.range (X.basicOpen (U := ⊤)) := by
    rw [← range_nonvanishingLocus_eq_range_basicOpen_of_mk_eq_one hL ⊤]
    exact ⟨s, rfl⟩
  let := hX.toField
  rw [← hr]
  obtain rfl | hr₀ := eq_or_ne r 0
  · exact Or.inl (X.basicOpen_zero ⊤)
  · exact Or.inr (X.basicOpen_of_isUnit hr₀.isUnit)

end TauCeti.AlgebraicGeometry.InvertibleSheaf
