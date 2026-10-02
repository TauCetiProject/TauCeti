/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Indecomposable
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Basic
public import TauCeti.RepresentationTheory.Quiver.Representation.DimensionVector
public import TauCeti.RepresentationTheory.Quiver.Subspace.Basic
public import TauCeti.RingTheory.AdjoinRoot.Basic
public import TauCeti.RingTheory.Polynomial.Truncated
public import Mathlib.CategoryTheory.PathCategory.MorphismProperty

/-!
# The four subspace quiver has infinite representation type

The subspace quiver with four outer vertices, whose underlying graph is the extended Dynkin
diagram `D̃₄`, has infinitely many finite-dimensional indecomposable representations over every
field. The family exhibited here is the nilpotent Jordan block in the guise of four subspaces:
writing `A = k[X]/(Xⁿ⁺¹)`, the representation `TauCeti.subspaceJordanRep k n` places `A × A` at
the centre and `A` at each outer vertex, and the four arrows embed `A` in `A × A` as

`x ↦ (x, 0)`, `x ↦ (0, x)`, `x ↦ (x, x)`, `x ↦ (x, X x)`,

that is as the two coordinate axes, the diagonal, and the graph of multiplication by `X`.

An endomorphism is forced, by naturality along the first two arrows, to act on the centre
coordinatewise through its components at the first two outer vertices; naturality along the
diagonal equates those two components, and naturality along the graph of `X` equates the fourth
with them and makes them commute with multiplication by `X`. So an endomorphism is multiplication
by a single element of `A`, its value at `1`, and the local ring `A` has no idempotent but `0` and
`1`: each representation is indecomposable. Their dimension vectors differ, so they are pairwise
non-isomorphic, and `TauCeti.not_isFiniteRepType_subspace_fin_four` follows over every field, with
no algebraic closedness and no infinitude of `k`.

The scalar family of the four subspace problem, the cross-ratio lines through `(1, c)` in `k²`
for `c ∉ {0, 1}`, would only settle the case of an infinite field.

## Main declarations

* `TauCeti.subspaceJordanRep`: the Jordan block `k[X]/(Xⁿ⁺¹)` as a configuration of four
  subspaces of `(k[X]/(Xⁿ⁺¹))²`.

## Main results

* `TauCeti.indecomposable_subspaceJordanRep`: these representations are indecomposable.
* `TauCeti.nonempty_subspaceJordanRep_iso_iff`: two of them are isomorphic exactly when their
  sizes agree.
* `TauCeti.not_isFiniteRepType_subspace_fin_four`: the four subspace quiver has infinite
  representation type over every field.

## Implementation notes

`TauCeti.subspaceJordanRep` carries `@[expose]` for the reason recorded on
`TauCeti.oneLoopNilpotentRep`: a functor built by `CategoryTheory.Paths.lift` reveals its vertex
spaces only through its definition, and the statements below need them to reduce.

## References

* I. M. Gelfand, V. A. Ponomarev, *Problems of linear algebra and classification of quadruples of
  subspaces in a finite-dimensional vector space*, Colloq. Math. Soc. János Bolyai **5** (1972),
  163--237.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Volume I, Chapter VII.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits Polynomial

universe u

variable (k : Type u) [Field k]

/-- **The Jordan block of size `n + 1` as four subspaces**: with `A = k[X]/(Xⁿ⁺¹)`, the
representation of the four subspace quiver with `A × A` at the centre, `A` at each outer vertex,
and the four arrows acting by `x ↦ (x, 0)`, `x ↦ (0, x)`, `x ↦ (x, x)` and `x ↦ (x, X x)`. -/
@[expose]
noncomputable def subspaceJordanRep (n : ℕ) : QuiverRep k (Quiver.Subspace (Fin 4)) :=
  Paths.lift
    { obj := fun v ↦ match v with
        | .center => ModuleCat.of k
            (AdjoinRoot ((X : k[X]) ^ (n + 1)) × AdjoinRoot ((X : k[X]) ^ (n + 1)))
        | .outer _ => ModuleCat.of k (AdjoinRoot ((X : k[X]) ^ (n + 1)))
      map := fun {a b} e ↦ match a, b, e with
        | .outer i, .center, _ => ModuleCat.ofHom
            (![LinearMap.inl k _ _, LinearMap.inr k _ _, LinearMap.id.prod LinearMap.id,
              LinearMap.id.prod (LinearMap.mulLeft k (AdjoinRoot.root ((X : k[X]) ^ (n + 1))))]
              i)
        | .center, .center, e => isEmptyElim e
        | .center, .outer _, e => isEmptyElim e
        | .outer _, .outer _, e => isEmptyElim e }

variable {k} {n : ℕ}

/-- The centre of `TauCeti.subspaceJordanRep` carries `(k[X]/(Xⁿ⁺¹))²`. -/
@[simp]
theorem subspaceJordanRep_obj_center :
    (subspaceJordanRep k n).obj (Quiver.Subspace.center : Paths (Quiver.Subspace (Fin 4))) =
      ModuleCat.of k (AdjoinRoot ((X : k[X]) ^ (n + 1)) × AdjoinRoot ((X : k[X]) ^ (n + 1))) :=
  rfl

/-- Each outer vertex of `TauCeti.subspaceJordanRep` carries `k[X]/(Xⁿ⁺¹)`. -/
@[simp]
theorem subspaceJordanRep_obj_outer (i : Fin 4) :
    (subspaceJordanRep k n).obj (Quiver.Subspace.outer i : Paths (Quiver.Subspace (Fin 4))) =
      ModuleCat.of k (AdjoinRoot ((X : k[X]) ^ (n + 1))) :=
  rfl

/-- The arrow indexed by `i` acts on `TauCeti.subspaceJordanRep` by the `i`-th of the four
embeddings. -/
private theorem subspaceJordanRep_map_arrow (i : Fin 4) :
    (subspaceJordanRep k n).map (Quiver.Subspace.arrow i).toPath = ModuleCat.ofHom
      (![LinearMap.inl k _ _, LinearMap.inr k _ _, LinearMap.id.prod LinearMap.id,
        LinearMap.id.prod (LinearMap.mulLeft k (AdjoinRoot.root ((X : k[X]) ^ (n + 1))))] i) :=
  Paths.lift_toPath _ _

/-- The first arrow embeds `k[X]/(Xⁿ⁺¹)` as the first coordinate axis. -/
@[simp]
theorem subspaceJordanRep_map_arrow_zero_apply (x : AdjoinRoot ((X : k[X]) ^ (n + 1))) :
    ((subspaceJordanRep k n).map (Quiver.Subspace.arrow 0).toPath).hom x = (x, 0) := by
  rw [subspaceJordanRep_map_arrow]
  rfl

/-- The second arrow embeds `k[X]/(Xⁿ⁺¹)` as the second coordinate axis. -/
@[simp]
theorem subspaceJordanRep_map_arrow_one_apply (x : AdjoinRoot ((X : k[X]) ^ (n + 1))) :
    ((subspaceJordanRep k n).map (Quiver.Subspace.arrow 1).toPath).hom x = (0, x) := by
  rw [subspaceJordanRep_map_arrow]
  rfl

/-- The third arrow embeds `k[X]/(Xⁿ⁺¹)` as the diagonal. -/
@[simp]
theorem subspaceJordanRep_map_arrow_two_apply (x : AdjoinRoot ((X : k[X]) ^ (n + 1))) :
    ((subspaceJordanRep k n).map (Quiver.Subspace.arrow 2).toPath).hom x = (x, x) := by
  rw [subspaceJordanRep_map_arrow]
  rfl

/-- The fourth arrow embeds `k[X]/(Xⁿ⁺¹)` as the graph of multiplication by `X`. -/
@[simp]
theorem subspaceJordanRep_map_arrow_three_apply (x : AdjoinRoot ((X : k[X]) ^ (n + 1))) :
    ((subspaceJordanRep k n).map (Quiver.Subspace.arrow 3).toPath).hom x =
      (x, AdjoinRoot.root ((X : k[X]) ^ (n + 1)) * x) := by
  rw [subspaceJordanRep_map_arrow]
  rfl

/-- `TauCeti.subspaceJordanRep k n` is finite-dimensional: its vertex spaces are `k[X]/(Xⁿ⁺¹)`
and its square. -/
theorem isFinDim_subspaceJordanRep :
    IsFinDim k (Quiver.Subspace (Fin 4)) (subspaceJordanRep k n) := by
  have := (monic_X_pow (R := k) (n + 1)).finite_adjoinRoot
  refine isFinDim_iff.mpr fun v ↦ ?_
  cases v
  · exact inferInstanceAs
      (FiniteDimensional k (AdjoinRoot ((X : k[X]) ^ (n + 1)) × AdjoinRoot ((X : k[X]) ^ (n + 1))))
  · exact inferInstanceAs (FiniteDimensional k (AdjoinRoot ((X : k[X]) ^ (n + 1))))

/-- The dimension of `k[X]/(Xⁿ⁺¹)`. -/
private theorem finrank_adjoinRoot_X_pow :
    Module.finrank k (AdjoinRoot ((X : k[X]) ^ (n + 1))) = n + 1 :=
  -- `AdjoinRoot f` *is* `k[X] ⧸ (f)`, so Mathlib's dimension formula for such a quotient applies.
  finrank_quotient_span_eq_natDegree.trans (natDegree_X_pow (n + 1))

/-- The dimension vector of `TauCeti.subspaceJordanRep k n` is `2 (n + 1)` at the centre. -/
theorem dimVector_subspaceJordanRep_center :
    dimVector (subspaceJordanRep k n) Quiver.Subspace.center = 2 * (n + 1) := by
  have := (monic_X_pow (R := k) (n + 1)).finite_adjoinRoot
  rw [dimVector_apply]
  -- The centre carries `(k[X]/(Xⁿ⁺¹))²` by definition, so the dimension of a product applies.
  exact Module.finrank_prod.trans (by rw [finrank_adjoinRoot_X_pow]; ring)

/-- The dimension vector of `TauCeti.subspaceJordanRep k n` is `n + 1` at each outer vertex. -/
theorem dimVector_subspaceJordanRep_outer (i : Fin 4) :
    dimVector (subspaceJordanRep k n) (Quiver.Subspace.outer i) = n + 1 :=
  (dimVector_apply _ _).trans finrank_adjoinRoot_X_pow

/-- `TauCeti.subspaceJordanRep k n` is nonzero: its outer vertex spaces are the nontrivial ring
`k[X]/(Xⁿ⁺¹)`. -/
theorem not_isZero_subspaceJordanRep : ¬ IsZero (subspaceJordanRep k n) := by
  intro h
  have : Subsingleton (AdjoinRoot ((X : k[X]) ^ (n + 1))) :=
    ModuleCat.subsingleton_of_isZero
      (h.obj (Quiver.Subspace.outer 0 : Paths (Quiver.Subspace (Fin 4))))
  exact false_of_nontrivial_of_subsingleton (AdjoinRoot ((X : k[X]) ^ (n + 1)))

/-! ### Endomorphisms -/

/-- The component of an endomorphism at the outer vertex indexed by `i`. -/
private noncomputable def outerApp (e : subspaceJordanRep k n ⟶ subspaceJordanRep k n)
    (i : Fin 4) : AdjoinRoot ((X : k[X]) ^ (n + 1)) →ₗ[k] AdjoinRoot ((X : k[X]) ^ (n + 1)) :=
  (e.app (Quiver.Subspace.outer i : Paths (Quiver.Subspace (Fin 4)))).hom

/-- The component of an endomorphism at the centre. -/
private noncomputable def centerApp (e : subspaceJordanRep k n ⟶ subspaceJordanRep k n) :
    AdjoinRoot ((X : k[X]) ^ (n + 1)) × AdjoinRoot ((X : k[X]) ^ (n + 1)) →ₗ[k]
      AdjoinRoot ((X : k[X]) ^ (n + 1)) × AdjoinRoot ((X : k[X]) ^ (n + 1)) :=
  (e.app (Quiver.Subspace.center : Paths (Quiver.Subspace (Fin 4)))).hom

/-- Naturality along the arrow indexed by `i`, read on an element. -/
private theorem centerApp_map_arrow (e : subspaceJordanRep k n ⟶ subspaceJordanRep k n)
    (i : Fin 4) (x : AdjoinRoot ((X : k[X]) ^ (n + 1))) :
    centerApp e (((subspaceJordanRep k n).map (Quiver.Subspace.arrow i).toPath).hom x) =
      ((subspaceJordanRep k n).map (Quiver.Subspace.arrow i).toPath).hom (outerApp e i x) :=
  congrArg (fun g ↦ (ModuleCat.Hom.hom g) x) (e.naturality (Quiver.Subspace.arrow i).toPath)

/-- Naturality along the two coordinate axes: the centre component of an endomorphism acts
coordinatewise, through the components at the first two outer vertices. -/
private theorem centerApp_mk (e : subspaceJordanRep k n ⟶ subspaceJordanRep k n)
    (x y : AdjoinRoot ((X : k[X]) ^ (n + 1))) :
    centerApp e (x, y) = (outerApp e 0 x, outerApp e 1 y) := by
  have h0 := centerApp_map_arrow e 0 x
  have h1 := centerApp_map_arrow e 1 y
  rw [subspaceJordanRep_map_arrow_zero_apply, subspaceJordanRep_map_arrow_zero_apply] at h0
  rw [subspaceJordanRep_map_arrow_one_apply, subspaceJordanRep_map_arrow_one_apply] at h1
  rw [← Prod.fst_add_snd (x, y), map_add]
  simp [h0, h1]

/-- **The four outer components of an endomorphism agree**: naturality along the diagonal equates
each of the first two with the third, and naturality along the graph of `X` equates the fourth
with the first. -/
private theorem outerApp_eq (e : subspaceJordanRep k n ⟶ subspaceJordanRep k n) (i : Fin 4) :
    outerApp e i = outerApp e 0 := by
  have h2 : ∀ x, outerApp e 0 x = outerApp e 2 x ∧ outerApp e 1 x = outerApp e 2 x := fun x ↦ by
    have h := centerApp_map_arrow e 2 x
    rw [subspaceJordanRep_map_arrow_two_apply, subspaceJordanRep_map_arrow_two_apply,
      centerApp_mk] at h
    exact Prod.mk.inj h
  have h3 : ∀ x, outerApp e 0 x = outerApp e 3 x := fun x ↦ by
    have h := centerApp_map_arrow e 3 x
    rw [subspaceJordanRep_map_arrow_three_apply, subspaceJordanRep_map_arrow_three_apply,
      centerApp_mk] at h
    exact (Prod.mk.inj h).1
  fin_cases i
  · rfl
  · exact LinearMap.ext fun x ↦ (h2 x).2.trans (h2 x).1.symm
  · exact LinearMap.ext fun x ↦ (h2 x).1.symm
  · exact LinearMap.ext fun x ↦ (h3 x).symm

/-- Naturality along the graph of `X`: the outer component commutes with multiplication by the
root. -/
private theorem outerApp_root_mul (e : subspaceJordanRep k n ⟶ subspaceJordanRep k n)
    (x : AdjoinRoot ((X : k[X]) ^ (n + 1))) :
    outerApp e 0 (AdjoinRoot.root ((X : k[X]) ^ (n + 1)) * x) =
      AdjoinRoot.root ((X : k[X]) ^ (n + 1)) * outerApp e 0 x := by
  have h := centerApp_map_arrow e 3 x
  rw [subspaceJordanRep_map_arrow_three_apply, subspaceJordanRep_map_arrow_three_apply,
    centerApp_mk, outerApp_eq e 1, outerApp_eq e 3] at h
  exact (Prod.mk.inj h).2

/-- **An endomorphism is multiplication by its value at `1`** at the first outer vertex, by
`TauCeti.AdjoinRoot.eq_mulRight_of_root_mul`. -/
private theorem outerApp_eq_mulRight (e : subspaceJordanRep k n ⟶ subspaceJordanRep k n) :
    outerApp e 0 = LinearMap.mulRight k (outerApp e 0 1) :=
  AdjoinRoot.eq_mulRight_of_root_mul (monic_X_pow (R := k) (n + 1)) (outerApp_root_mul e)

/-- **An endomorphism is determined by its component at the first outer vertex.** -/
private theorem hom_ext_of_outerApp {e e' : subspaceJordanRep k n ⟶ subspaceJordanRep k n}
    (h : outerApp e 0 = outerApp e' 0) : e = e' := by
  refine NatTrans.ext (funext fun v ↦ ?_)
  cases v with
  | center =>
    refine ModuleCat.hom_ext (LinearMap.ext fun p ↦ ?_)
    -- The component at the centre, applied to `p = (p.1, p.2)`, is `centerApp` by definition.
    change centerApp e (p.1, p.2) = centerApp e' (p.1, p.2)
    rw [centerApp_mk, centerApp_mk, outerApp_eq e 1, outerApp_eq e' 1, h]
  | outer i =>
    refine ModuleCat.hom_ext ?_
    -- The component at an outer vertex is `outerApp` by definition.
    change outerApp e i = outerApp e' i
    rw [outerApp_eq e i, outerApp_eq e' i, h]

/-- **`TauCeti.subspaceJordanRep k n` is indecomposable.** An endomorphism is multiplication by
its value at `1` at the first outer vertex and is determined by it, so that value records the
endomorphism faithfully in `k[X]/(Xⁿ⁺¹)`, a local ring (`TauCeti.isLocalRing_adjoinRoot_X_pow`),
sending `0` to `0`, the identity to `1` and squares to squares. -/
theorem indecomposable_subspaceJordanRep : Indecomposable (subspaceJordanRep k n) := by
  refine indecomposable_of_injective_of_isLocalRing not_isZero_subspaceJordanRep
    (fun e ↦ outerApp e 0 1) (fun e e' h ↦ ?_) rfl rfl
    fun e ↦ ?_
  · refine hom_ext_of_outerApp ?_
    rw [outerApp_eq_mulRight e, outerApp_eq_mulRight e']
    exact congrArg (LinearMap.mulRight k) h
  · change outerApp e 0 (outerApp e 0 1) = _
    rw [outerApp_eq_mulRight e]
    simp

/-- **Jordan blocks of different sizes give non-isomorphic configurations**: their dimension
vectors differ. -/
theorem eq_of_nonempty_subspaceJordanRep_iso {m n : ℕ}
    (h : Nonempty (subspaceJordanRep k m ≅ subspaceJordanRep k n)) : m = n := by
  obtain ⟨e⟩ := h
  have hd := congrFun (dimVector_eq_of_iso e) (Quiver.Subspace.outer 0)
  rw [dimVector_subspaceJordanRep_outer, dimVector_subspaceJordanRep_outer] at hd
  omega

/-- Two of the representations `TauCeti.subspaceJordanRep k n` are isomorphic exactly when their
sizes agree. -/
@[simp]
theorem nonempty_subspaceJordanRep_iso_iff {m n : ℕ} :
    Nonempty (subspaceJordanRep k m ≅ subspaceJordanRep k n) ↔ m = n :=
  ⟨eq_of_nonempty_subspaceJordanRep_iso, by rintro rfl; exact ⟨Iso.refl _⟩⟩

/-- **The four subspace quiver has infinite representation type over every field.** Its underlying
graph is the extended Dynkin diagram `D̃₄`. The representations `TauCeti.subspaceJordanRep k n` are
finite-dimensional, indecomposable and pairwise non-isomorphic, so `ℕ` indexes an infinite family
of them. -/
theorem not_isFiniteRepType_subspace_fin_four (k : Type u) [Field k] :
    ¬ IsFiniteRepType.{u, 0, 1, u} k (Quiver.Subspace (Fin 4)) :=
  not_isFiniteRepType_of_infinite (M := subspaceJordanRep k) (fun _ ↦ isFinDim_subspaceJordanRep)
    (fun _ ↦ indecomposable_subspaceJordanRep)
    fun _ _ hne h ↦ hne (eq_of_nonempty_subspaceJordanRep_iso h)

end TauCeti
