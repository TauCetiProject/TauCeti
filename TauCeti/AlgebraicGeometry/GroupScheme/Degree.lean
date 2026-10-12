/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import TauCeti.AlgebraicGeometry.GroupScheme.FiniteFlat
public import TauCeti.AlgebraicGeometry.GroupScheme.Kernel
import TauCeti.AlgebraicGeometry.GroupScheme.KilledByRank
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank
import TauCeti.CategoryTheory.Monoidal.Grp.KernelPair

/-!
# The degree of a finite locally free homomorphism of group schemes

Let `f : G ⟶ H` be a homomorphism of group schemes over a scheme `S` whose underlying morphism of
schemes is finite and flat. Its scheme-theoretic kernel is the base change of `f` along the unit
section of `H` (`TauCeti.GroupScheme.isPullback_kernel_scheme`), so it is finite and flat over
`S`. The **degree** of `f` is the function `GroupScheme.degree f : S → ℕ` whose value at `s` is the
rank of the kernel at `s`. When `f` is also locally of finite presentation it is locally constant,
but over a disconnected base it need not be constant. For an isogeny of elliptic curves, a finite,
flat and surjective homomorphism, this is its degree.

The degree of `f` controls the rank of `f` itself. If `f` is moreover surjective, then the rank of
`f` at a point `x` of `H` is the degree of `f` at the image of `x` in `S`
(`GroupScheme.finrank_hom_hom_left`): the base change of `f` along itself is the projection
`ker f ×_S G ⟶ G`, by the kernel-pair identity `TauCeti.isPullback_mul_of_isPullback_one`. Hence the
degree is multiplicative under composition, and `f` is an isomorphism exactly when its degree is
`1`.

If `G` is commutative and `f` is locally of finite presentation, the kernel is a finite locally
free commutative group scheme (`GroupScheme.finiteFlatKernel`). By Deligne's theorem
(`TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme.pow_eq_one_of_finrank`), if `f` has
constant degree `n` then its kernel is killed by `n`. For an isogeny of elliptic curves this says
that its kernel lies in the `n`-torsion, which is what makes the dual isogeny of a degree-`n`
isogeny constructible as a factorisation of multiplication by `n`.

## Main definitions

* `TauCeti.GroupScheme.degree f`: the rank of the kernel of `f`, a function on the base.
* `TauCeti.GroupScheme.finiteFlatKernel f`: the kernel of a finite locally free homomorphism out of
  a commutative group scheme, as a finite locally free commutative group scheme.

## Main results

* `TauCeti.GroupScheme.isLocallyConstant_degree`: the degree is locally constant.
* `TauCeti.GroupScheme.degree_pos`: the degree is positive.
* `TauCeti.GroupScheme.degree_pullback_mapGrp_map`: the degree is stable under base change.
* `TauCeti.GroupScheme.finrank_hom_hom_left`: for surjective `f`, the rank of `f` at a point is the
  degree at its image in the base.
* `TauCeti.GroupScheme.degree_comp`: the degree is multiplicative under composition.
* `TauCeti.GroupScheme.isIso_iff_degree_eq_one`: a finite, flat and surjective homomorphism is an
  isomorphism exactly when its degree is `1`; in particular an isomorphism has degree `1`
  (`TauCeti.GroupScheme.degree_eq_one_of_isIso`).
* `TauCeti.GroupScheme.kernel_ι_pow_eq_one`: the kernel of a homomorphism of constant degree `n`
  out of a commutative group scheme is killed by `n`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics
  Studies 108, Princeton University Press, 1985, §1.12 and Chapter 2.
* The Stacks Project, [Tag 02KA](https://stacks.math.columbia.edu/tag/02KA), for the rank of a
  finite locally free morphism.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonObj

universe u

namespace TauCeti.GroupScheme

variable {S : Scheme.{u}} {G H K : Grp (Over S)} (f : G ⟶ H)

/-- **The degree of a homomorphism of group schemes** `f : G ⟶ H` over `S`: the function on `S`
whose value at `s` is the rank of the kernel of `f` at `s`. It is meaningful when `f` is finite and
flat, so that its kernel is finite and flat over `S`. -/
noncomputable def degree : S → ℕ :=
  (kernel f).X.hom.finrank

/-- The rank of the kernel of `f` is the degree of `f`. -/
@[simp]
theorem finrank_kernel_hom : (kernel f).X.hom.finrank = degree f :=
  (rfl)

section FiniteFlat

variable [IsFinite f.hom.hom.left] [Flat f.hom.hom.left]

/-- **The degree is the rank over the unit section.** For a finite flat homomorphism `f : G ⟶ H`,
the degree of `f` at `s` is the rank of `f` at the image of `s` under the unit section of `H`. -/
theorem degree_eq_finrank (s : S) : degree f s = f.hom.hom.left.finrank (η[H.X].left s) :=
  Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_kernel_scheme f) s

/-- **The degree is locally constant** for a finite locally free homomorphism of group schemes. -/
theorem isLocallyConstant_degree [LocallyOfFinitePresentation f.hom.hom.left] :
    IsLocallyConstant (degree f) :=
  (kernel f).X.hom.isLocallyConstant_finrank

/-- The degree of a finite flat homomorphism of group schemes is positive: the unit section of the
target lies in the image. -/
theorem degree_pos (s : S) : 0 < degree f s := by
  rw [degree_eq_finrank, ← IsMonHom.one_hom f.hom.hom, Over.comp_left, Scheme.Hom.comp_apply]
  exact f.hom.hom.left.one_le_finrank_map _

/-- **The degree is stable under base change.** For a finite flat homomorphism `f : G ⟶ H` over
`S` and a morphism `s : T ⟶ S`, the degree of the base change of `f` to `T` at `t` is the degree
of `f` at `s t`: the kernel of the base change is the base change of the kernel
(`kernelBaseChangeIso`). -/
@[simp]
theorem degree_pullback_mapGrp_map {T : Scheme.{u}} (s : T ⟶ S) (t : T) :
    degree ((Over.pullback s).mapGrp.map f) t = degree f (s t) := by
  -- The kernel of the base change is isomorphic over `T` to the base change `P` of the kernel,
  -- which lies over `T` by the second projection.
  let P := ((Over.pullback s).mapGrp.obj (kernel f)).X
  have : Flat P.hom := inferInstanceAs (Flat (pullback.snd (kernel f).X.hom s))
  have : IsFinite P.hom := inferInstanceAs (IsFinite (pullback.snd (kernel f).X.hom s))
  have : IsIso (kernelBaseChangeIso s f).inv.hom.hom.left :=
    inferInstanceAs
      (IsIso ((Grp.forget (Over T) ⋙ Over.forget T).map (kernelBaseChangeIso s f).inv))
  rw [degree, ← Over.w (kernelBaseChangeIso s f).inv.hom.hom,
    Scheme.Hom.finrank_comp_left_of_isIso]
  exact Scheme.Hom.finrank_pullback_snd _ _ t

variable [Surjective f.hom.hom.left]

/-- **The rank of a finite flat surjective homomorphism is its degree, fibrewise.** For a finite,
flat and surjective homomorphism `f : G ⟶ H` of group schemes over `S`, the rank of `f` at a point
`x` of `H` is the degree of `f` at the image of `x` in `S`. -/
theorem finrank_hom_hom_left (x : H.X.left) :
    f.hom.hom.left.finrank x = degree f (H.X.hom x) := by
  obtain ⟨y, rfl⟩ := f.hom.hom.left.surjective x
  -- The base change of `f` along itself is the projection `ker f ×_S G ⟶ G`.
  have h := (isPullback_mul_of_isPullback_one f.hom.hom (kernel.ι f).hom.hom
    (isPullback_kernel_hom f)).map (Over.forget S)
  simp only [Over.forget_map, Over.snd_left] at h
  rw [← Scheme.Hom.finrank_of_isPullback _ _ _ _ h y, Scheme.Hom.finrank_pullback_snd,
    ← Scheme.Hom.comp_apply, Over.w f.hom.hom, finrank_kernel_hom]

/-- **The degree is multiplicative.** If `f : G ⟶ H` is finite, flat and surjective and
`g : H ⟶ K` is finite and flat, the degree of `f ≫ g` at `s` is the product of the degrees of `f`
and of `g` at `s`. -/
@[simp]
theorem degree_comp (g : H ⟶ K) [IsFinite g.hom.hom.left] [Flat g.hom.hom.left] (s : S) :
    degree (f ≫ g) s = degree f s * degree g s := by
  have hfg : (f ≫ g).hom.hom.left = f.hom.hom.left ≫ g.hom.hom.left := by simp
  have : IsFinite (f ≫ g).hom.hom.left := by rw [hfg]; infer_instance
  have : Flat (f ≫ g).hom.hom.left := by rw [hfg]; infer_instance
  -- The rank of `f` at a point of `H` is the degree of `f` at its image in `S`.
  have hf : f.hom.hom.left.finrank = (fun z ↦ degree f (K.X.hom z)) ∘ g.hom.hom.left := by
    ext y
    rw [finrank_hom_hom_left, Function.comp_apply, ← Scheme.Hom.comp_apply, Over.w g.hom.hom]
  rw [degree_eq_finrank, hfg, Scheme.Hom.finrank_comp_of_finrank_eq_comp _ _ hf,
    ← degree_eq_finrank, ← Scheme.Hom.comp_apply, Over.w η[K.X]]
  simp

/-- **A homomorphism of degree one is an isomorphism.** A finite, flat and surjective
homomorphism of group schemes is an isomorphism exactly when its degree is `1` at every point. -/
theorem isIso_iff_degree_eq_one : IsIso f ↔ degree f = 1 := by
  -- `f` is an isomorphism exactly when its underlying morphism of schemes is.
  have hiso : IsIso f ↔ IsIso f.hom.hom.left := by
    refine ⟨fun _ ↦ inferInstanceAs (IsIso ((Over.forget S).map f.hom.hom)), fun h ↦ ?_⟩
    apply (isIso_iff_of_reflects_iso f (Grp.forget₂Mon (Over S))).mp
    apply (isIso_iff_of_reflects_iso f.hom (Mon.forget (Over S))).mp
    exact (isIso_iff_of_reflects_iso f.hom.hom (Over.forget S)).mp h
  rw [hiso, Scheme.Hom.isIso_iff_finrank_eq]
  refine ⟨fun h ↦ funext fun s ↦ ?_, fun h ↦ funext fun x ↦ ?_⟩
  · rw [degree_eq_finrank]
    exact congrFun h _
  · rw [finrank_hom_hom_left, h, Pi.one_apply, Pi.one_apply]

end FiniteFlat

/-- An isomorphism of group schemes has degree `1`. -/
@[simp]
theorem degree_eq_one_of_isIso [IsIso f] : degree f = 1 :=
  have : IsIso f.hom.hom.left := inferInstanceAs (IsIso ((Over.forget S).map f.hom.hom))
  (isIso_iff_degree_eq_one f).mp ‹_›

/-! ### The kernel as a finite locally free commutative group scheme -/

section Commutative

variable [IsCommMonObj G.X] [IsFinite f.hom.hom.left] [Flat f.hom.hom.left]
  [LocallyOfFinitePresentation f.hom.hom.left]

/-- The kernel of a finite locally free homomorphism `f` out of a commutative group scheme, as a
finite locally free commutative group scheme over `S`. -/
noncomputable def finiteFlatKernel : AlgebraicGeometry.FiniteFlatCommGroupScheme S where
  carrier := (kernel f).X.left
  structureMap := (kernel f).X.hom
  grp := inferInstanceAs (GrpObj (kernel f).X)
  comm := inferInstanceAs (IsCommMonObj (kernel f).X)
  finite := inferInstance
  flat := inferInstance
  locallyOfFinitePresentation := inferInstance

/-- The rank of `finiteFlatKernel f` is the degree of `f`. -/
@[simp]
theorem finrank_finiteFlatKernel_structureMap :
    (finiteFlatKernel f).structureMap.finrank = degree f :=
  (rfl)

/-- The group object underlying `finiteFlatKernel f` is the kernel of `f`. -/
@[simp]
theorem grpMk_finiteFlatKernel : Grp.mk (finiteFlatKernel f).toOver = kernel f :=
  (rfl)

/-- **The kernel of a homomorphism of degree `n` is killed by `n`.** Let `f : G ⟶ H` be a finite
locally free homomorphism of group schemes over `S`, with `G` commutative, whose degree is `n` at
every point of `S`. Then the kernel inclusion, as a point of `G` with values in the kernel, is
killed by `n`. -/
theorem kernel_ι_pow_eq_one {n : ℕ} (hn : ∀ s, degree f s = n) :
    (kernel.ι f).hom.hom ^ n = 1 := by
  -- Deligne's theorem for `finiteFlatKernel f`, whose underlying object of `Over S` is
  -- `(kernel f).X` (`grpMk_finiteFlatKernel`).
  have h : (𝟙 (kernel f).X) ^ n = 1 :=
    (finiteFlatKernel f).pow_eq_one_of_finrank
      (fun s ↦ by rw [finrank_finiteFlatKernel_structureMap, hn]) (𝟙 _)
  rw [← Category.id_comp (kernel.ι f).hom.hom, ← MonObj.pow_comp, h, MonObj.one_comp]

end Commutative

end TauCeti.GroupScheme
