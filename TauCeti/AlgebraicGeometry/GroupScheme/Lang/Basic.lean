/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Frobenius.GroupScheme
public import TauCeti.AlgebraicGeometry.GroupScheme.Kernel
public import TauCeti.AlgebraicGeometry.GroupScheme.MultiplicativeGroup
public import TauCeti.CategoryTheory.Monoidal.Cartesian.CommGrp

/-!
# The Lang map of a commutative group scheme over a finite field

Let `k` be a finite field with `q = p ^ a` elements and `G` a commutative group scheme over `k`,
with `q`-power Frobenius `F : G ⟶ G`. The *Lang map* of `G` is the endomorphism `L = F − id` of
`G` as a commutative group scheme, written additively in the endomorphism group of `G`; on
points, with the group law of `G` written multiplicatively, it is `g ↦ F(g) · g⁻¹`.

Because it is a difference of two homomorphisms of commutative group schemes, `L` is again a
homomorphism, and every homomorphism `φ : G ⟶ H` of commutative group schemes over `k` intertwines
the Lang maps of `G` and `H`, since it commutes with Frobenius. Taking `φ = F` shows that `L`
commutes with `F`.

The scheme-theoretic kernel of `L` is the group scheme of fixed points of Frobenius: a point
`x : T ⟶ G` over `k` factors through it exactly when `F_T ≫ x = x`, where `F_T` is the `q`-power
Frobenius of the test scheme `T`. Every `k`-rational point of `G` is fixed, so the `k`-rational
points of the kernel are those of `G`.

The norm `N = 1 + F + ⋯ + F^{n-1}` relates the Lang map to the `n`-th power of Frobenius, which is
the `q ^ n`-power Frobenius: `N ∘ L = L ∘ N = F ^ n − 1`. Hence `N` carries the points fixed by
`F ^ n`, such as the rational points over the extension of `k` of degree `n`, into the kernel of
`L`.

For the multiplicative group `𝔾_m` over `k`, whose points with values in `T` are the units of
`Γ(T, 𝒪_T)`, Frobenius raises a unit to its `q`-th power, the Lang map raises it to its
`(q − 1)`-th power, and the kernel of the Lang map has as points the units `u` with
`u ^ (q - 1) = 1`.

For smooth connected `G` of finite type, Lang's theorem says moreover that `L` is surjective and
a finite étale torsor under the finite group `G(k)`; that is not proved here.

## Main definitions

* `TauCeti.GroupScheme.langMap k a ha G`: the Lang map `F − id` of a commutative group scheme `G`
  over `k`.
* `TauCeti.GroupScheme.langKernel k a ha G`: the scheme-theoretic kernel of the Lang map, with
  inclusion `TauCeti.GroupScheme.langKernelι k a ha G`; a point of `G` fixed by Frobenius lifts to
  it by `TauCeti.GroupScheme.langKernelLift`.
* `TauCeti.GroupScheme.frobeniusNorm k a ha G n`: the norm `1 + F + ⋯ + F^{n-1}`.

## Main results

* `TauCeti.GroupScheme.comp_langMap_hom_hom_hom`: on a point `x : T ⟶ G`, the Lang map is
  `(F_T ≫ x) / x`.
* `TauCeti.GroupScheme.langMap_naturality`: homomorphisms of commutative group schemes commute with
  the Lang maps.
* `TauCeti.GroupScheme.exists_comp_langKernelι_iff`: a point of `G` factors through the kernel of
  the Lang map if and only if it is fixed by Frobenius.
* `TauCeti.GroupScheme.langKernelRationalPointsMulEquiv`: the `k`-rational points of the kernel of
  the Lang map are the `k`-rational points of `G`.
* `TauCeti.GroupScheme.frobeniusNorm_comp_langMap` and
  `TauCeti.GroupScheme.langMap_comp_frobeniusNorm`: `N ∘ L = L ∘ N = F ^ n − 1`.
* `TauCeti.GroupScheme.comp_frobeniusNorm_hom_hom_hom`: on a point `x : T ⟶ G`, the norm is the
  product of the points `F_T ^ i ≫ x` for `i < n`.
* `TauCeti.GroupScheme.exists_comp_langKernelι_eq_comp_frobeniusNorm`: the norm of a point fixed by
  `F ^ n` lies in the kernel of the Lang map.
* `TauCeti.GroupScheme.Gm.pointsMulEquiv_comp_langMap`: the Lang map of `𝔾_m` is `u ↦ u ^ (q - 1)`
  on points.

## References

* S. Lang, *Algebraic groups over finite fields*, Amer. J. Math. 78 (1956), 555–563.
* G. Laumon, *Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil*, Publ. Math. IHÉS 65 (1987), §1.1.3.
* P. Deligne, *Sommes trig.*, in SGA 4½, Lecture Notes in Math. 569, Springer, 1977, §1.
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace TauCeti.GroupScheme

universe u

variable (k : Type u) [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] (a : ℕ)
  (ha : Nat.card k = p ^ a)

/-! ### The Lang map -/

section LangMap

variable (G : CommGrp (Over (Spec (CommRingCat.of k))))

/-- **The Lang map** `L = F − id` of a commutative group scheme `G` over a finite field `k` with
`q = p ^ a` elements, where `F` is the `q`-power Frobenius of `G`. It is an endomorphism of `G` as
a commutative group scheme; on points it is `g ↦ F(g) · g⁻¹`. -/
noncomputable def langMap : G ⟶ G :=
  qPowerFrobeniusCommGrpHom k a ha G - 𝟙 G

/-- The Lang map is the difference of the `q`-power Frobenius and the identity. -/
theorem langMap_def : langMap k a ha G = qPowerFrobeniusCommGrpHom k a ha G - 𝟙 G :=
  (rfl)

/-- The underlying morphism of the Lang map is the quotient of the `q`-power Frobenius of `G` by
the identity of `G`, for the group law on points. -/
@[simp]
theorem langMap_hom_hom_hom :
    (langMap k a ha G).hom.hom.hom = qPowerFrobeniusOver k a ha G.X / 𝟙 G.X := by
  simp [langMap_def]

variable {G}

/-- **The Lang map on points.** For a point `x : T ⟶ G` over `k`, the Lang map sends `x` to the
quotient of `F_T ≫ x` by `x`, where `F_T` is the `q`-power Frobenius of `T`. -/
theorem comp_langMap_hom_hom_hom {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ G.X) :
    x ≫ (langMap k a ha G).hom.hom.hom = (qPowerFrobeniusOver k a ha T ≫ x) / x := by
  rw [langMap_hom_hom_hom, GrpObj.comp_div, comp_qPowerFrobeniusOver, Category.comp_id]

/-- **Naturality of the Lang map.** Every homomorphism `φ : G ⟶ H` of commutative group schemes
over `k` intertwines the Lang maps of `G` and `H`. For `φ` the `q`-power Frobenius of `G`, this
says that the Lang map commutes with Frobenius. -/
@[reassoc]
theorem langMap_naturality {H : CommGrp (Over (Spec (CommRingCat.of k)))} (φ : G ⟶ H) :
    langMap k a ha G ≫ φ = φ ≫ langMap k a ha H := by
  rw [langMap_def, langMap_def, Preadditive.sub_comp, Preadditive.comp_sub,
    qPowerFrobeniusCommGrpHom_naturality, Category.id_comp, Category.comp_id]

end LangMap

/-! ### The kernel of the Lang map -/

section LangKernel

variable (G : CommGrp (Over (Spec (CommRingCat.of k))))

/-- **The kernel of the Lang map** of a commutative group scheme `G` over `k`: the
scheme-theoretic kernel of `F − id`, the group scheme of fixed points of the `q`-power
Frobenius. -/
noncomputable def langKernel : Grp (Over (Spec (CommRingCat.of k))) :=
  kernel ((CommGrp.forget₂Grp _).map (langMap k a ha G))

/-- The inclusion of the kernel of the Lang map into `G`, a morphism of `Over (Spec k)`. -/
noncomputable def langKernelι : (langKernel k a ha G).X ⟶ G.X :=
  (kernel.ι ((CommGrp.forget₂Grp _).map (langMap k a ha G))).hom.hom

/-- The inclusion of the kernel of the Lang map is a homomorphism of group schemes. -/
instance isMonHom_langKernelι : IsMonHom (langKernelι k a ha G) :=
  (kernel.ι ((CommGrp.forget₂Grp _).map (langMap k a ha G))).hom.isMonHom_hom

/-- The inclusion of the kernel of the Lang map is a monomorphism. -/
instance mono_langKernelι : Mono (langKernelι k a ha G) :=
  mono_kernel_ι_hom _

/-- The kernel of the Lang map is commutative. -/
instance isCommMonObj_langKernel : IsCommMonObj (langKernel k a ha G).X :=
  -- the group object underlying `G` in `Grp (Over S)` has the same carrier `G.X`
  have : IsCommMonObj ((CommGrp.forget₂Grp _).obj G).X := inferInstanceAs (IsCommMonObj G.X)
  isCommMonObj_kernel _

/-- **The kernel of the Lang map is the fibre of the Lang map over the unit section.** -/
theorem isPullback_langKernelι :
    IsPullback (langKernelι k a ha G) (toUnit _) (langMap k a ha G).hom.hom.hom η[G.X] :=
  isPullback_kernel_hom ((CommGrp.forget₂Grp _).map (langMap k a ha G))

variable {G}

/-- A point `x : T ⟶ G` is killed by the Lang map viewed as a homomorphism of group schemes if and
only if it is killed by the Lang map of `G` as a commutative group scheme. -/
private theorem comp_forget₂Grp_map_langMap_eq_one_iff {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ G.X) :
    x ≫ ((CommGrp.forget₂Grp _).map (langMap k a ha G)).hom.hom = 1 ↔
      x ≫ (langMap k a ha G).hom.hom.hom = 1 := by
  rw [CommGrp.forget₂Grp_map_hom]
  -- `Iff.rfl`: the group object `(CommGrp.forget₂Grp _).obj G` has carrier `G.X` with the same
  -- group structure, so the unit points `1 : T ⟶ G.X` on the two sides agree by definition.
  exact Iff.rfl

/-- A point `x : T ⟶ G` over `k` factors through the kernel of the Lang map if and only if the
Lang map kills it. -/
theorem exists_comp_langKernelι_iff_comp_langMap {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ G.X) :
    (∃ y, y ≫ langKernelι k a ha G = x) ↔ x ≫ (langMap k a ha G).hom.hom.hom = 1 :=
  (exists_comp_kernel_ι_hom_iff (f := (CommGrp.forget₂Grp _).map (langMap k a ha G)) x).trans
    (comp_forget₂Grp_map_langMap_eq_one_iff k a ha x)

variable (G) in
/-- The Lang map kills its kernel: the inclusion of the kernel followed by the Lang map is the unit
point. -/
@[reassoc]
theorem langKernelι_comp_langMap_hom_hom_hom :
    langKernelι k a ha G ≫ (langMap k a ha G).hom.hom.hom = 1 :=
  (exists_comp_langKernelι_iff_comp_langMap k a ha _).1 ⟨𝟙 _, Category.id_comp _⟩

/-- **Points of the kernel of the Lang map.** A point `x : T ⟶ G` over `k` factors through the
kernel of the Lang map if and only if it is fixed by Frobenius: `F_T ≫ x = x`, where `F_T` is the
`q`-power Frobenius of `T`. -/
theorem exists_comp_langKernelι_iff {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ G.X) :
    (∃ y, y ≫ langKernelι k a ha G = x) ↔ qPowerFrobeniusOver k a ha T ≫ x = x := by
  rw [← div_eq_one, ← comp_langMap_hom_hom_hom, exists_comp_langKernelι_iff_comp_langMap]

variable (G) in
/-- Frobenius acts as the identity on the scheme-theoretic Lang kernel. -/
@[simp]
theorem qPowerFrobeniusOver_langKernel :
    qPowerFrobeniusOver k a ha (langKernel k a ha G).X = 𝟙 _ := by
  apply (cancel_mono (langKernelι k a ha G)).mp
  rw [Category.id_comp]
  exact (exists_comp_langKernelι_iff k a ha _).mp ⟨𝟙 _, Category.id_comp _⟩

/-- Every `k`-rational point of `G` factors through the kernel of the Lang map: the `q`-power
Frobenius of `Spec k` is the identity. -/
theorem exists_comp_langKernelι (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X) :
    ∃ y, y ≫ langKernelι k a ha G = x :=
  (exists_comp_langKernelι_iff k a ha x).2 (by simp)

/-- The point of the kernel of the Lang map given by a point `x : T ⟶ G` over `k` fixed by
Frobenius: `F_T ≫ x = x`, where `F_T` is the `q`-power Frobenius of `T`. -/
noncomputable def langKernelLift {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ G.X)
    (hx : qPowerFrobeniusOver k a ha T ≫ x = x) : T ⟶ (langKernel k a ha G).X :=
  kernelLift x <| (comp_forget₂Grp_map_langMap_eq_one_iff k a ha x).2 <| by
    rw [comp_langMap_hom_hom_hom, hx, div_self']

/-- The point `langKernelLift x hx` of the kernel of the Lang map maps to `x` in `G`. -/
@[reassoc (attr := simp)]
theorem langKernelLift_ι {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ G.X)
    (hx : qPowerFrobeniusOver k a ha T ≫ x = x) :
    langKernelLift k a ha x hx ≫ langKernelι k a ha G = x :=
  kernelLift_ι _ _

/-- Two points of the kernel of the Lang map agree if their images in `G` do. -/
theorem langKernel_hom_ext {T : Over (Spec (CommRingCat.of k))}
    {y y' : T ⟶ (langKernel k a ha G).X}
    (h : y ≫ langKernelι k a ha G = y' ≫ langKernelι k a ha G) : y = y' :=
  (cancel_mono _).1 h

variable (G)

/-- **The `k`-rational points of the kernel of the Lang map** are the `k`-rational points of `G`:
composition with the inclusion of the kernel is an isomorphism of groups. -/
noncomputable def langKernelRationalPointsMulEquiv :
    (𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ (langKernel k a ha G).X) ≃*
      (𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X) :=
  MulEquiv.ofBijective (IsMonHom.monoidHom (langKernelι k a ha G) _)
    ⟨fun _ _ h ↦ (cancel_mono (langKernelι k a ha G)).1 h,
      fun x ↦ exists_comp_langKernelι k a ha x⟩

@[simp]
theorem langKernelRationalPointsMulEquiv_apply
    (y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ (langKernel k a ha G).X) :
    langKernelRationalPointsMulEquiv k a ha G y = y ≫ langKernelι k a ha G :=
  (rfl)

end LangKernel

/-! ### The norm and the Lang maps of powers of Frobenius -/

section Norm

variable (G : CommGrp (Over (Spec (CommRingCat.of k))))

/-- **The norm** `N = 1 + F + ⋯ + F^{n-1}` of a commutative group scheme `G` over `k`, an
endomorphism of `G` as a commutative group scheme, where `F` is the `q`-power Frobenius. It carries
the points fixed by `F ^ n` into the kernel of the Lang map
(`TauCeti.GroupScheme.exists_comp_langKernelι_eq_comp_frobeniusNorm`). -/
noncomputable def frobeniusNorm (n : ℕ) : G ⟶ G :=
  (∑ i ∈ Finset.range n, End.of (qPowerFrobeniusCommGrpHom k a ha G) ^ i).asHom

/-- The empty norm is zero. -/
@[simp]
theorem frobeniusNorm_zero : frobeniusNorm k a ha G 0 = 0 := by
  simp [frobeniusNorm]

/-- The norm `1 + F + ⋯ + F^n` is the norm `1 + F + ⋯ + F^{n-1}` plus `F ^ n`. -/
@[simp]
theorem frobeniusNorm_succ (n : ℕ) :
    frobeniusNorm k a ha G (n + 1) =
      frobeniusNorm k a ha G n + (End.of (qPowerFrobeniusCommGrpHom k a ha G) ^ n).asHom := by
  simp [frobeniusNorm, Finset.sum_range_succ]

variable {G} in
/-- **The norm on points.** For a point `x : T ⟶ G` over `k`, the norm sends `x` to the product of
the points `F_T ^ i ≫ x` for `i < n`, where `F_T` is the `q`-power Frobenius of `T`. -/
theorem comp_frobeniusNorm_hom_hom_hom {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ G.X)
    (n : ℕ) : x ≫ (frobeniusNorm k a ha G n).hom.hom.hom =
      ∏ i ∈ Finset.range n, (End.of (qPowerFrobeniusOver k a ha T) ^ i).asHom ≫ x := by
  induction n with
  | zero => rw [frobeniusNorm_zero, CommGrp.zero_hom_hom_hom, comp_one, Finset.prod_range_zero]
  | succ n ih =>
    rw [frobeniusNorm_succ, CommGrp.add_hom_hom_hom, comp_mul, ih,
      qPowerFrobeniusCommGrpHom_pow_hom_hom_hom, comp_qPowerFrobeniusOver_pow,
      Finset.prod_range_succ]

/-- The Lang map is `F − 1` in the endomorphism ring of `G`. -/
theorem langMap_eq_asHom :
    langMap k a ha G = (End.of (qPowerFrobeniusCommGrpHom k a ha G) - 1).asHom := by
  simp [langMap_def]

/-- **Telescoping.** The norm followed by the Lang map is `F ^ n − 1`, where `F ^ n` is the
`q ^ n`-power Frobenius (`AlgebraicGeometry.Scheme.qPowerFrobeniusOver_pow_asHom_left`). -/
theorem frobeniusNorm_comp_langMap (n : ℕ) :
    frobeniusNorm k a ha G n ≫ langMap k a ha G =
      (End.of (qPowerFrobeniusCommGrpHom k a ha G) ^ n).asHom - 𝟙 G := by
  rw [langMap_eq_asHom, frobeniusNorm, ← End.mul_asHom, mul_geom_sum]
  simp

/-- **Telescoping.** The Lang map followed by the norm is `F ^ n − 1`. -/
theorem langMap_comp_frobeniusNorm (n : ℕ) :
    langMap k a ha G ≫ frobeniusNorm k a ha G n =
      (End.of (qPowerFrobeniusCommGrpHom k a ha G) ^ n).asHom - 𝟙 G := by
  rw [langMap_eq_asHom, frobeniusNorm, ← End.mul_asHom, geom_sum_mul]
  simp

variable {G}

/-- **The norm lands in the kernel of the Lang map.** If a point `x : T ⟶ G` over `k` is fixed by
the `n`-th power of the `q`-power Frobenius of `T`, for instance a `k_n`-rational point for the
extension `k_n` of `k` of degree `n`, then its norm factors through the kernel of the Lang map. -/
theorem exists_comp_langKernelι_eq_comp_frobeniusNorm {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ G.X) (n : ℕ)
    (hx : (End.of (qPowerFrobeniusOver k a ha T) ^ n).asHom ≫ x = x) :
    ∃ y, y ≫ langKernelι k a ha G = x ≫ (frobeniusNorm k a ha G n).hom.hom.hom := by
  have h : (frobeniusNorm k a ha G n).hom.hom.hom ≫ (langMap k a ha G).hom.hom.hom =
      (End.of (qPowerFrobeniusOver k a ha G.X) ^ n).asHom / 𝟙 G.X := by
    simpa using congrArg (fun f ↦ f.hom.hom.hom) (frobeniusNorm_comp_langMap k a ha G n)
  rw [exists_comp_langKernelι_iff_comp_langMap, Category.assoc, h, GrpObj.comp_div,
    comp_qPowerFrobeniusOver_pow, hx, Category.comp_id, div_self']

end Norm

/-! ### The Lang map of the multiplicative group -/

namespace Gm

variable {T : Over (Spec (CommRingCat.of k))}

include ha in
omit [Field k] [CharP k p] in
/-- The finite field `k` with `p ^ a` elements has nonzero cardinality. -/
private theorem natCard_ne_zero : Nat.card k ≠ 0 :=
  ha ▸ pow_ne_zero a (Fact.out : p.Prime).ne_zero

/-- **Frobenius on the points of `𝔾_m`.** The `q`-power Frobenius of the test scheme `T` raises the
unit of `Γ(T, 𝒪_T)` attached to a point of `𝔾_m` to its `q`-th power. -/
theorem pointsMulEquiv_qPowerFrobeniusOver_comp (x : T ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    pointsMulEquiv T (qPowerFrobeniusOver k a ha T ≫ x) = pointsMulEquiv T x ^ Nat.card k := by
  rw [pointsMulEquiv_naturality]
  ext
  simp

/-- **The Lang map of `𝔾_m`** raises the unit of `Γ(T, 𝒪_T)` attached to a point to its
`(q − 1)`-th power. -/
theorem pointsMulEquiv_comp_langMap (x : T ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    pointsMulEquiv T (x ≫ (langMap k a ha (GmCommGrp (Spec (CommRingCat.of k)))).hom.hom.hom) =
      pointsMulEquiv T x ^ (Nat.card k - 1) := by
  rw [comp_langMap_hom_hom_hom k a ha (G := GmCommGrp (Spec (CommRingCat.of k))), map_div,
    pointsMulEquiv_qPowerFrobeniusOver_comp, ← pow_sub_one_mul (natCard_ne_zero k a ha),
    mul_div_cancel_right]

/-- **The kernel of the Lang map of `𝔾_m`.** A point of `𝔾_m` with values in `T` factors through
the kernel of the Lang map if and only if the attached unit `u` of `Γ(T, 𝒪_T)` satisfies
`u ^ (q - 1) = 1`. -/
theorem exists_comp_langKernelι_iff (x : T ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    (∃ y, y ≫ langKernelι k a ha (GmCommGrp (Spec (CommRingCat.of k))) = x) ↔
      pointsMulEquiv T x ^ (Nat.card k - 1) = 1 := by
  rw [GroupScheme.exists_comp_langKernelι_iff, ← (pointsMulEquiv T).injective.eq_iff,
    pointsMulEquiv_qPowerFrobeniusOver_comp, ← pow_sub_one_mul (natCard_ne_zero k a ha),
    mul_eq_right]

end Gm

end TauCeti.GroupScheme
