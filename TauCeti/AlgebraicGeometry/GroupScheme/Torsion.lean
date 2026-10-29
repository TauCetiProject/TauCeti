/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.Kernel
public import TauCeti.AlgebraicGeometry.GroupScheme.KilledByRank
public import TauCeti.CategoryTheory.Monoidal.Cartesian.CommGrp
import TauCeti.CategoryTheory.Preadditive.CoprimeKernels

/-!
# Torsion of commutative group schemes, transitions, and the coprime splitting

Let `G` be a commutative group scheme over a scheme `S`, that is, a commutative group object of
`Over S`, and let `n` be an integer. The `n`-torsion `G[n]` is the scheme-theoretic kernel of
multiplication by `n`, the integer `n` of the endomorphism ring `End_S(G)`. Its points with values
in any `Z` over `S` are the points of `G` killed by `n`.

Multiplication by `m` restricts to a homomorphism `G[mn] ⟶ G[n]`, and `G[m]` includes into
`G[mn]`. The transitions satisfy identity and composition laws, with transports between equal
indices. These laws supply the coherence of towers of prime-power torsion.
The transition is a base change of multiplication by `m`, and its scheme-theoretic kernel is
the included `G[m]`.

If `G` is killed by `m * n`, with `m` and `n` coprime, then addition `G[m] ×_S G[n] ⟶ G` is an
isomorphism of group schemes over `S`. If `a * m + b * n = 1`, the projection of `G` to `G[m]` is
multiplication by `b * n`, and the projection to `G[n]` is multiplication by `a * m`. By Deligne's
theorem this applies to every finite locally free commutative group scheme over `S` of constant rank
`m * n`. Katz and Mazur use this splitting to reduce statements about level structures, such as the
generators of a finite locally free group scheme, to the prime-power case.

The argument is the splitting of an object of a preadditive category killed by a product of coprime
integers (`CategoryTheory.Limits.BinaryBicone.isBilimitOfCoprimeKernelForks`), applied in the
preadditive category `CommGrp (Over S)`.

The definition of `G[n]` and its points API generalize the `n`-torsion of an elliptic curve in
`TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/Geom/Torsion.lean`
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.torsion`, identified with a kernel by
`TauCeti.AlgebraicGeometry.EllipticCurveGeom.torsion_eq_kernel`, together with its `torsionι`,
`torsionLift`, `torsionPointsMulEquiv`, and `torsionMap`) from elliptic curves to arbitrary
commutative group schemes.

## Main definitions

* `TauCeti.GroupScheme.torsion G n`: the `n`-torsion `G[n]`, a group object of `Over S`.
* `TauCeti.GroupScheme.torsionι G n`: its inclusion `G[n] ⟶ G`.
* `TauCeti.GroupScheme.torsionLift`: the point of `G[n]` given by a point of `G` killed by `n`.
* `TauCeti.GroupScheme.torsionMap`: the homomorphism `G[n] ⟶ H[n]` induced by a homomorphism
  `G ⟶ H`.
* `TauCeti.GroupScheme.torsionPointsMulEquiv`: the points of `G[n]` with values in `Z`, as a group,
  are the `n`-torsion of the points of `G` with values in `Z`.
* `TauCeti.GroupScheme.torsionBaseChangeIso`: formation of `G[n]` commutes with base change.
* `TauCeti.GroupScheme.torsionMulBy`: multiplication `G[mn] ⟶ G[n]` between torsion levels.
* `TauCeti.GroupScheme.torsionInclusion`: the inclusion `G[m] ⟶ G[mn]`.
* `TauCeti.GroupScheme.torsionTensorIso`: for `G` killed by `m * n` with `m` and `n` coprime, the
  isomorphism `G[m] ×_S G[n] ≅ G` of group schemes given by addition.

## Main results

* `TauCeti.GroupScheme.exists_comp_torsionι_iff`: the points of `G[n]` are the points of `G`
  killed by `n`.
* `TauCeti.GroupScheme.isPullback_torsionι`: `G[n]` is the fibre of multiplication by `n` over the
  unit section.
* `TauCeti.GroupScheme.torsionBaseChangeIso_hom_hom_hom_comp_torsionMap`: the base-change
  comparison for the `n`-torsion is natural in `G`.
* `TauCeti.GroupScheme.isIso_tensorHom_torsionι_comp_mul`: for `G` killed by `m * n` with `m` and
  `n` coprime, addition `G[m] ×_S G[n] ⟶ G` is an isomorphism.
* `TauCeti.GroupScheme.torsionTensorIso_inv_hom_hom_fst_torsionι` and
  `TauCeti.GroupScheme.torsionTensorIso_inv_hom_hom_snd_torsionι`: its inverse is given by
  multiplication by `b * n` and by `a * m`, for every Bézout identity `a * m + b * n = 1`.
* `TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme.isIso_tensorHom_torsionι_comp_mul`: a finite
  locally free commutative group scheme of constant rank `m * n`, with `m` and `n` coprime, is the
  product of its `m`-torsion and its `n`-torsion.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics
  Studies 108, Princeton University Press, 1985, 1.10.14–1.10.15, 2.3.1 and Chapter 5.
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace TauCeti.GroupScheme

universe u

variable {S : Scheme.{u}} (G : CommGrp (Over S))

/-! ### The `n`-torsion of a commutative group scheme -/

/-- **The `n`-torsion `G[n]` of a commutative group scheme** `G` over `S`: the scheme-theoretic
kernel of multiplication by `n`, the integer `n` of the endomorphism ring of `G`, as a group object
of `Over S`. -/
noncomputable def torsion (n : ℤ) : Grp (Over S) :=
  kernel ((CommGrp.forget₂Grp (Over S)).map (n : End G).asHom)

/-- The torsion group scheme is the kernel of multiplication by its index. -/
theorem torsion_eq_kernel (n : ℤ) :
    torsion G n = kernel ((CommGrp.forget₂Grp (Over S)).map (n : End G).asHom) :=
  (rfl)

/-- The inclusion `G[n] ⟶ G` of the `n`-torsion of `G`, a morphism of `Over S`. -/
noncomputable def torsionι (n : ℤ) : (torsion G n).X ⟶ G.X :=
  (kernel.ι ((CommGrp.forget₂Grp (Over S)).map (n : End G).asHom)).hom.hom

/-- The inclusion of the `n`-torsion is a homomorphism of group schemes over `S`. -/
instance isMonHom_torsionι (n : ℤ) : IsMonHom (torsionι G n) :=
  (kernel.ι ((CommGrp.forget₂Grp (Over S)).map (n : End G).asHom)).hom.isMonHom_hom

/-- The inclusion of the `n`-torsion is a monomorphism. -/
instance mono_torsionι (n : ℤ) : Mono (torsionι G n) :=
  mono_kernel_ι_hom _

/-- **The `n`-torsion is commutative.** Its group law is the restriction of that of `G`. -/
instance isCommMonObj_torsion (n : ℤ) : IsCommMonObj (torsion G n).X :=
  -- the group object underlying `G` in `Grp (Over S)` has the same carrier `G.X`
  have : IsCommMonObj ((CommGrp.forget₂Grp (Over S)).obj G).X := inferInstanceAs (IsCommMonObj G.X)
  isCommMonObj_kernel _

/-- The inclusion of the `n`-torsion, followed by multiplication by `n`, is the unit point. -/
@[reassoc]
theorem torsionι_comp_zpow (n : ℤ) : torsionι G n ≫ 𝟙 G.X ^ n = 1 := by
  have h := kernel_ι_comp_hom ((CommGrp.forget₂Grp (Over S)).map (n : End G).asHom)
  rw [CommGrp.forget₂Grp_map_hom, CommGrp.intCast_hom_hom_hom] at h
  exact h

/-- The inclusion of the `n`-torsion, as a point of `G` with values in `G[n]`, is killed by `n`. -/
@[simp]
theorem torsionι_zpow (n : ℤ) : torsionι G n ^ n = 1 := by
  rw [← torsionι_comp_zpow G n, GrpObj.comp_zpow, Category.comp_id]

/-- **The `n`-torsion is the fibre of multiplication by `n` over the unit section.** -/
theorem isPullback_torsionι (n : ℤ) :
    IsPullback (torsionι G n) (toUnit _) (𝟙 G.X ^ n) η[G.X] := by
  have h := isPullback_kernel_hom ((CommGrp.forget₂Grp (Over S)).map (n : End G).asHom)
  rw [CommGrp.forget₂Grp_map_hom, CommGrp.intCast_hom_hom_hom] at h
  exact h

/-- Two points of the `n`-torsion agree if their images in `G` do. -/
theorem torsion_hom_ext {n : ℤ} {Z : Over S} {y y' : Z ⟶ (torsion G n).X}
    (h : y ≫ torsionι G n = y' ≫ torsionι G n) : y = y' :=
  kernel_hom_ext h

variable {G} {n : ℤ} {Z : Over S}

/-- The point of the `n`-torsion of `G` given by a point `x` of `G` killed by `n`. -/
noncomputable def torsionLift (x : Z ⟶ G.X) (hx : x ^ n = 1) : Z ⟶ (torsion G n).X :=
  kernelLift x (by
    have h : x ≫ 𝟙 G.X ^ n = 1 := by rw [GrpObj.comp_zpow, Category.comp_id, hx]
    rw [CommGrp.forget₂Grp_map_hom, CommGrp.intCast_hom_hom_hom]
    exact h)

/-- The point `torsionLift x hx` of the `n`-torsion maps to `x` in `G`. -/
@[reassoc (attr := simp)]
theorem torsionLift_ι (x : Z ⟶ G.X) (hx : x ^ n = 1) : torsionLift x hx ≫ torsionι G n = x :=
  kernelLift_ι _ _

/-- **The points of the `n`-torsion.** A point of `G` factors through `G[n]` if and only if it is
killed by `n`. -/
theorem exists_comp_torsionι_iff (x : Z ⟶ G.X) : (∃ y, y ≫ torsionι G n = x) ↔ x ^ n = 1 := by
  refine ⟨?_, fun hx ↦ ⟨torsionLift x hx, torsionLift_ι x hx⟩⟩
  rintro ⟨y, rfl⟩
  rw [← GrpObj.comp_zpow, torsionι_zpow, comp_one]

/-- A homomorphism into `G` killed by `n` factors through the `n`-torsion as a homomorphism. -/
instance isMonHom_torsionLift {Z : Over S} [MonObj Z] (x : Z ⟶ G.X) [IsMonHom x]
    (hx : x ^ n = 1) : IsMonHom (torsionLift x hx) where
  one_hom := torsion_hom_ext G (by simp)
  mul_hom := torsion_hom_ext G (by simp [IsMonHom.mul_hom])

/-! ### Transitions between torsion levels -/

section Transitions

variable (G) (m n : ℤ)

/-- Multiplication by `m` restricted to `G[mn]`, with values in `G[n]`. -/
noncomputable def torsionMulBy : (torsion G (m * n)).X ⟶ (torsion G n).X :=
  torsionLift (torsionι G (m * n) ≫ 𝟙 G.X ^ m) (by
    rw [GrpObj.comp_zpow, Category.comp_id, ← zpow_mul, torsionι_zpow])

/-- The transition `G[mn] ⟶ G[n]` sends a torsion point to its multiple by `m`. -/
@[reassoc (attr := simp)]
theorem torsionMulBy_torsionι :
    torsionMulBy G m n ≫ torsionι G n = torsionι G (m * n) ^ m := by
  rw [torsionMulBy, torsionLift_ι, GrpObj.comp_zpow, Category.comp_id]

/-- The torsion transition is a homomorphism of group schemes. -/
instance isMonHom_torsionMulBy : IsMonHom (torsionMulBy G m n) := by
  have : IsMonHom (𝟙 G.X ^ m) := by
    rw [← CommGrp.intCast_hom_hom_hom]
    infer_instance
  unfold torsionMulBy
  infer_instance

/-- The inclusion of `G[m]` in `G[mn]`. -/
noncomputable def torsionInclusion : (torsion G m).X ⟶ (torsion G (m * n)).X :=
  torsionLift (torsionι G m) (by rw [zpow_mul, torsionι_zpow, one_zpow])

/-- The inclusion between torsion levels preserves the underlying point of `G`. -/
@[reassoc (attr := simp)]
theorem torsionInclusion_torsionι :
    torsionInclusion G m n ≫ torsionι G (m * n) = torsionι G m :=
  torsionLift_ι _ _

/-- The inclusion between torsion levels is a monomorphism. -/
instance mono_torsionInclusion : Mono (torsionInclusion G m n) :=
  mono_of_mono_fac (torsionInclusion_torsionι G m n)

/-- The inclusion between torsion levels is a homomorphism of group schemes. -/
instance isMonHom_torsionInclusion : IsMonHom (torsionInclusion G m n) := by
  unfold torsionInclusion
  infer_instance

/-- The transition kills the included `m`-torsion. -/
@[reassoc (attr := simp)]
theorem torsionInclusion_torsionMulBy :
    torsionInclusion G m n ≫ torsionMulBy G m n = 1 := by
  apply torsion_hom_ext G
  simp [GrpObj.comp_zpow]

/-- The torsion transition is the base change of multiplication by `m` on `G`. -/
theorem isPullback_torsionMulBy :
    IsPullback (torsionι G (m * n)) (torsionMulBy G m n)
      (𝟙 G.X ^ m) (torsionι G n) := by
  refine (IsPullback.of_right ?_ ?_ (isPullback_torsionι G n).flip).flip
  · simpa [GrpObj.comp_zpow, ← zpow_mul, mul_comm n m] using
      (isPullback_torsionι G (m * n)).flip
  · simp [GrpObj.comp_zpow]

/-- The scheme-theoretic kernel of `G[mn] ⟶ G[n]` is the included `G[m]`. -/
theorem isPullback_torsionInclusion :
    IsPullback (torsionInclusion G m n) (toUnit _)
      (torsionMulBy G m n) η[(torsion G n).X] := by
  refine IsPullback.of_right ?_ ?_ (isPullback_torsionMulBy G m n)
  · simpa using isPullback_torsionι G m
  · rw [torsionInclusion_torsionMulBy, Hom.one_def]

/-- Transport between equal torsion indices preserves the underlying point of `G`. -/
@[reassoc (attr := simp)]
theorem eqToHom_torsionι {a b : ℤ} (h : a = b) :
    eqToHom (congrArg (fun k ↦ (torsion G k).X) h) ≫ torsionι G b = torsionι G a := by
  subst b
  simp

/-- Inclusion into the same torsion level is the identity, after identifying `m * 1` with `m`. -/
@[simp]
theorem torsionInclusion_one :
    torsionInclusion G m 1 = eqToHom (congrArg (fun k ↦ (torsion G k).X) (mul_one m).symm) := by
  apply torsion_hom_ext G
  simp

/-- Successive torsion inclusions multiply their indices, with the associativity transport. -/
@[reassoc (attr := simp)]
theorem torsionInclusion_comp (l : ℤ) :
    torsionInclusion G m n ≫ torsionInclusion G (m * n) l =
      torsionInclusion G m (n * l) ≫
        eqToHom (congrArg (fun k ↦ (torsion G k).X) (mul_assoc m n l).symm) := by
  apply torsion_hom_ext G
  simp only [Category.assoc, torsionInclusion_torsionι,
    eqToHom_torsionι G (mul_assoc m n l).symm]

/-- Multiplication by one on torsion is the identity, after identifying `1 * n` with `n`. -/
@[simp]
theorem torsionMulBy_one :
    torsionMulBy G 1 n = eqToHom (congrArg (fun k ↦ (torsion G k).X) (one_mul n)) := by
  apply torsion_hom_ext G
  simp

/-- Successive torsion transitions multiply their indices, with the associativity transport. -/
@[reassoc (attr := simp)]
theorem torsionMulBy_comp (l : ℤ) :
    torsionMulBy G l (m * n) ≫ torsionMulBy G m n =
      eqToHom (congrArg (fun k ↦ (torsion G k).X) (mul_assoc l m n).symm) ≫
        torsionMulBy G (l * m) n := by
  apply torsion_hom_ext G
  simp only [Category.assoc, torsionMulBy_torsionι, GrpObj.comp_zpow,
    eqToHom_torsionι G (mul_assoc l m n).symm, ← zpow_mul]

end Transitions

variable (G n Z)

/-- **The points of the `n`-torsion.** The points of `G[n]` with values in `Z` form the `n`-torsion
subgroup of the commutative group of points of `G` with values in `Z`. -/
noncomputable def torsionPointsMulEquiv :
    (Z ⟶ (torsion G n).X) ≃* (zpowGroupHom n : (Z ⟶ G.X) →* (Z ⟶ G.X)).ker :=
  (kernelPointsMulEquiv _ Z).trans <| MulEquiv.subgroupCongr <|
    congrArg MonoidHom.ker <| MonoidHom.ext fun (x : Z ⟶ G.X) ↦
      (congrArg (x ≫ ·) (CommGrp.intCast_hom_hom_hom G n)).trans <|
        (GrpObj.comp_zpow x (𝟙 G.X) n).trans (congrArg (· ^ n) (Category.comp_id x))

/-- A point of the `n`-torsion corresponds to its image in `G`. -/
@[simp]
theorem coe_torsionPointsMulEquiv_apply (y : Z ⟶ (torsion G n).X) :
    (torsionPointsMulEquiv G n Z y : Z ⟶ G.X) = y ≫ torsionι G n :=
  coe_kernelPointsMulEquiv_apply _ Z y

/-- The point of the `n`-torsion corresponding to a point `x` of `G` killed by `n` maps to `x` in
`G`. -/
@[simp]
theorem torsionPointsMulEquiv_symm_apply_torsionι
    (x : (zpowGroupHom n : (Z ⟶ G.X) →* (Z ⟶ G.X)).ker) :
    (torsionPointsMulEquiv G n Z).symm x ≫ torsionι G n = x :=
  kernelPointsMulEquiv_symm_apply_ι _ Z _

variable {n Z}

/-! ### Functoriality of the `n`-torsion -/

variable {G} {H K : CommGrp (Over S)}

/-- A homomorphism of commutative group schemes commutes with multiplication by `n`. -/
private theorem forget₂Grp_map_intCast_comp (f : G ⟶ H) (n : ℤ) :
    (CommGrp.forget₂Grp (Over S)).map (n : End G).asHom ≫ (CommGrp.forget₂Grp (Over S)).map f =
      (CommGrp.forget₂Grp (Over S)).map f ≫
        (CommGrp.forget₂Grp (Over S)).map (n : End H).asHom := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  refine congrArg _ (CommGrp.hom_ext _ _ ?_)
  simp [GrpObj.zpow_comp, GrpObj.comp_zpow]

/-- The homomorphism `G[n] ⟶ H[n]` induced by a homomorphism `f : G ⟶ H` of commutative group
schemes over `S`, the restriction of `f` to the `n`-torsion. -/
noncomputable def torsionMap (f : G ⟶ H) (n : ℤ) : (torsion G n).X ⟶ (torsion H n).X :=
  (kernel.map _ _ _ _ (forget₂Grp_map_intCast_comp f n)).hom.hom

/-- The map induced on the `n`-torsion by `f` is the restriction of `f`. -/
@[reassoc (attr := simp)]
theorem torsionMap_ι (f : G ⟶ H) (n : ℤ) :
    torsionMap f n ≫ torsionι H n = torsionι G n ≫ f.hom.hom.hom :=
  congrArg (fun g ↦ g.hom.hom) (kernel.lift_ι _ _ _ :
    kernel.map _ _ _ _ (forget₂Grp_map_intCast_comp f n) ≫ kernel.ι _ = _)

/-- The map induced on the `n`-torsion is a homomorphism of group schemes over `S`. -/
instance isMonHom_torsionMap (f : G ⟶ H) (n : ℤ) : IsMonHom (torsionMap f n) :=
  (kernel.map _ _ _ _ (forget₂Grp_map_intCast_comp f n)).hom.isMonHom_hom

/-- Torsion transitions commute with homomorphisms of commutative group schemes. -/
@[reassoc (attr := simp)]
theorem torsionMulBy_comp_torsionMap (f : G ⟶ H) (m n : ℤ) :
    torsionMulBy G m n ≫ torsionMap f n =
      torsionMap f (m * n) ≫ torsionMulBy H m n := by
  apply torsion_hom_ext H
  simp [GrpObj.comp_zpow, GrpObj.zpow_comp]

/-- Inclusions between torsion levels commute with homomorphisms of commutative group schemes. -/
@[reassoc (attr := simp)]
theorem torsionInclusion_comp_torsionMap (f : G ⟶ H) (m n : ℤ) :
    torsionInclusion G m n ≫ torsionMap f (m * n) =
      torsionMap f m ≫ torsionInclusion H m n := by
  apply torsion_hom_ext H
  simp

/-- The identity of `G` induces the identity of `G[n]`. -/
@[simp]
theorem torsionMap_id (n : ℤ) : torsionMap (𝟙 G) n = 𝟙 _ :=
  torsion_hom_ext G (by simp)

/-- The map induced on the `n`-torsion by a composite is the composite of the induced maps. -/
@[simp]
theorem torsionMap_comp (f : G ⟶ H) (g : H ⟶ K) (n : ℤ) :
    torsionMap (f ≫ g) n = torsionMap f n ≫ torsionMap g n :=
  torsion_hom_ext K (by simp)

variable (G)

/-! ### Base change of the `n`-torsion -/

/-- Base change along `s : T ⟶ S` takes multiplication by `n` on `G` to multiplication by `n` on
the base change of `G`. -/
private theorem pullback_mapGrp_map_intCast {T : Scheme.{u}} (s : T ⟶ S) (n : ℤ) :
    (Over.pullback s).mapGrp.map ((CommGrp.forget₂Grp (Over S)).map (n : End G).asHom) =
      (CommGrp.forget₂Grp (Over T)).map (n : End ((Over.pullback s).mapCommGrp.obj G)).asHom := by
  ext : 2
  rw [Functor.mapGrp_map_hom_hom, CommGrp.forget₂Grp_map_hom, CommGrp.forget₂Grp_map_hom,
    CommGrp.intCast_hom_hom_hom, CommGrp.intCast_hom_hom_hom]
  exact congrArg Over.Hom.left <| (map_zpow (Over.pullback s).homMonoidHom (𝟙 G.X) n).trans
    (congrArg (· ^ n) ((Over.pullback s).map_id G.X))

/-- **Formation of the `n`-torsion commutes with base change.** The canonical isomorphism from the
base change of `G[n]` along `s : T ⟶ S` to the `n`-torsion of the base change of `G`. -/
noncomputable def torsionBaseChangeIso {T : Scheme.{u}} (s : T ⟶ S) (n : ℤ) :
    (Over.pullback s).mapGrp.obj (torsion G n) ≅
      torsion ((Over.pullback s).mapCommGrp.obj G) n :=
  kernelBaseChangeIso s _ ≪≫ kernelIsoOfEq (pullback_mapGrp_map_intCast G s n)

/-- The base-change comparison for the `n`-torsion intertwines the two inclusions. -/
@[reassoc (attr := simp)]
theorem torsionBaseChangeIso_hom_hom_hom_torsionι {T : Scheme.{u}} (s : T ⟶ S) (n : ℤ) :
    (torsionBaseChangeIso G s n).hom.hom.hom ≫ torsionι ((Over.pullback s).mapCommGrp.obj G) n =
      (Over.pullback s).map (torsionι G n) := by
  -- the inclusion of the base change of `G[n]` is the base change of the inclusion of `G[n]`
  have h := ((Category.assoc _ _ _).trans ((kernelBaseChangeIso s _).hom ≫=
    kernelIsoOfEq_hom_comp_ι (pullback_mapGrp_map_intCast G s n))).trans
      (kernelBaseChangeIso_hom_comp_ι s _)
  exact congrArg (fun f ↦ f.hom.hom) h

variable {G} in
/-- The base-change comparison for the `n`-torsion is natural: it intertwines the base change of
the map induced on the `n`-torsion by `f` with the map induced by the base change of `f`. -/
@[reassoc]
theorem torsionBaseChangeIso_hom_hom_hom_comp_torsionMap (f : G ⟶ H) {T : Scheme.{u}}
    (s : T ⟶ S) (n : ℤ) :
    (torsionBaseChangeIso G s n).hom.hom.hom ≫ torsionMap ((Over.pullback s).mapCommGrp.map f) n =
      (Over.pullback s).map (torsionMap f n) ≫ (torsionBaseChangeIso H s n).hom.hom.hom :=
  torsion_hom_ext _ <| by
    -- the carriers of the two base changes agree only up to defeq, so reassociate by terms
    refine ((Category.assoc _ _ _).trans ?_).trans <| ((Over.pullback s).map (torsionMap f n) ≫=
      torsionBaseChangeIso_hom_hom_hom_torsionι H s n).symm.trans (Category.assoc _ _ _).symm
    rw [torsionMap_ι, torsionBaseChangeIso_hom_hom_hom_torsionι_assoc]
    -- both sides are the base change of `torsionι G n ≫ f = torsionMap f n ≫ torsionι H n`
    exact ((Over.pullback s).map_comp _ _).symm.trans <|
      (congrArg (Over.pullback s).map (torsionMap_ι f n).symm).trans
        ((Over.pullback s).map_comp _ _)

/-! ### The `n`-torsion as a kernel in `CommGrp (Over S)` -/

/-- The `n`-torsion of `G`, as a commutative group object of `Over S`. -/
private noncomputable abbrev torsionCommGrp (n : ℤ) : CommGrp (Over S) :=
  { X := (torsion G n).X }

/-- The `n`-torsion of `G` as a kernel fork of multiplication by `n` in the preadditive category
`CommGrp (Over S)`. -/
private noncomputable abbrev torsionKernelFork (n : ℤ) : KernelFork (n • 𝟙 G) :=
  KernelFork.ofι (Z := torsionCommGrp G n) (CommGrp.homMk (torsionι G n))
    (by ext; simp)

/-- A morphism into `G` of `CommGrp (Over S)` killed by multiplication by `n` is, as a point of
`G`, killed by `n`. -/
private theorem hom_hom_hom_zpow_eq_one {n : ℤ} {W : CommGrp (Over S)} {k : W ⟶ G}
    (hk : k ≫ (n • 𝟙 G) = 0) : k.hom.hom.hom ^ n = 1 := by
  rw [← CommGrp.zsmul_hom_hom_hom, ← Category.comp_id k, ← Preadditive.comp_zsmul, hk,
    CommGrp.zero_hom_hom_hom]

/-- The inclusion of `torsionKernelFork` is `torsionι` on underlying morphisms of `Over S`. -/
private theorem comp_homMk_torsionι_hom_hom_hom {n : ℤ} {W : CommGrp (Over S)}
    (l : W ⟶ torsionCommGrp G n) :
    (l ≫ CommGrp.homMk (torsionι G n)).hom.hom.hom = l.hom.hom.hom ≫ torsionι G n := by
  simp only [CommGrp.comp_hom, Grp.comp', Mon.comp_hom', CommGrp.homMk_hom_hom_hom]

/-- The `n`-torsion of `G` is a kernel of multiplication by `n` in `CommGrp (Over S)`. -/
private noncomputable def isLimitTorsionKernelFork (n : ℤ) : IsLimit (torsionKernelFork G n) :=
  KernelFork.IsLimit.ofι _ _
    (fun {W} k hk ↦ CommGrp.homMk (A := W) (B := torsionCommGrp G n)
      (torsionLift k.hom.hom.hom (hom_hom_hom_zpow_eq_one G hk)))
    (fun k hk ↦ CommGrp.hom_ext _ _ (by
      rw [comp_homMk_torsionι_hom_hom_hom, CommGrp.homMk_hom_hom_hom, torsionLift_ι]))
    (fun k hk l hl ↦ CommGrp.hom_ext _ _ (torsion_hom_ext G (by
      rw [← comp_homMk_torsionι_hom_hom_hom, hl, CommGrp.homMk_hom_hom_hom, torsionLift_ι])))

/-! ### The coprime splitting -/

variable {G} {a b m n : ℤ}

/-- A commutative group scheme whose points are killed by `k` is killed by the integer `k` of its
endomorphism ring. -/
private theorem zsmul_id_eq_zero {k : ℤ} (hG : 𝟙 G.X ^ k = 1) : k • 𝟙 G = 0 :=
  CommGrp.hom_ext _ _ (by simpa using hG)

variable (hab : a * m + b * n = 1) (hG : 𝟙 G.X ^ (m * n) = 1)

/-- The splitting of `G` as the biproduct of `G[m]` and `G[n]` in `CommGrp (Over S)`. -/
private noncomputable abbrev torsionBicone :
    BinaryBicone (torsionCommGrp G m) (torsionCommGrp G n) :=
  BinaryBicone.ofCoprimeKernelForks hab (zsmul_id_eq_zero hG) (isLimitTorsionKernelFork G m)
    (isLimitTorsionKernelFork G n)

/-- The projection of `G` to `G[m]`, the first projection of `torsionBicone`. -/
private noncomputable def torsionFst : G.X ⟶ (torsion G m).X :=
  (torsionBicone hab hG).fst.hom.hom.hom

/-- The projection of `G` to `G[n]`, the second projection of `torsionBicone`. -/
private noncomputable def torsionSnd : G.X ⟶ (torsion G n).X :=
  (torsionBicone hab hG).snd.hom.hom.hom

private instance : IsMonHom (torsionFst hab hG) :=
  (torsionBicone hab hG).fst.hom.hom.isMonHom_hom

private instance : IsMonHom (torsionSnd hab hG) :=
  (torsionBicone hab hG).snd.hom.hom.isMonHom_hom

/-- The projection of `G` to `G[m]` is multiplication by `b * n`. -/
@[reassoc]
private theorem torsionFst_torsionι : torsionFst hab hG ≫ torsionι G m = 𝟙 G.X ^ (b * n) := by
  simpa [torsionFst, torsionSnd, Grp.comp_hom_hom] using congrArg (fun f ↦ f.hom.hom.hom)
    (BinaryBicone.ofCoprimeKernelForks_fst_ι hab (zsmul_id_eq_zero hG)
      (isLimitTorsionKernelFork G m) (isLimitTorsionKernelFork G n))

/-- The projection of `G` to `G[n]` is multiplication by `a * m`. -/
@[reassoc]
private theorem torsionSnd_torsionι : torsionSnd hab hG ≫ torsionι G n = 𝟙 G.X ^ (a * m) := by
  simpa [torsionFst, torsionSnd, Grp.comp_hom_hom] using congrArg (fun f ↦ f.hom.hom.hom)
    (BinaryBicone.ofCoprimeKernelForks_snd_ι hab (zsmul_id_eq_zero hG)
      (isLimitTorsionKernelFork G m) (isLimitTorsionKernelFork G n))

/-- The projection to `G[m]` restricts to the identity on `G[m]`. -/
@[reassoc]
private theorem torsionι_torsionFst : torsionι G m ≫ torsionFst hab hG = 𝟙 _ := by
  simpa [torsionFst, torsionSnd, Grp.comp_hom_hom] using
    congrArg (fun f ↦ f.hom.hom.hom) (torsionBicone hab hG).inl_fst

/-- The projection to `G[n]` kills `G[m]`. -/
@[reassoc]
private theorem torsionι_torsionSnd : torsionι G m ≫ torsionSnd hab hG = 1 := by
  simpa [torsionFst, torsionSnd, Grp.comp_hom_hom] using
    congrArg (fun f ↦ f.hom.hom.hom) (torsionBicone hab hG).inl_snd

/-- The projection to `G[m]` kills `G[n]`. -/
@[reassoc]
private theorem torsionι_torsionFst' : torsionι G n ≫ torsionFst hab hG = 1 := by
  simpa [torsionFst, torsionSnd, Grp.comp_hom_hom] using
    congrArg (fun f ↦ f.hom.hom.hom) (torsionBicone hab hG).inr_fst

/-- The projection to `G[n]` restricts to the identity on `G[n]`. -/
@[reassoc]
private theorem torsionι_torsionSnd' : torsionι G n ≫ torsionSnd hab hG = 𝟙 _ := by
  simpa [torsionFst, torsionSnd, Grp.comp_hom_hom] using
    congrArg (fun f ↦ f.hom.hom.hom) (torsionBicone hab hG).inr_snd

/-- Addition `G[m] ×_S G[n] ⟶ G` is the product of the two inclusions for the group law on
points. -/
private theorem tensorHom_torsionι_comp_mul :
    (torsionι G m ⊗ₘ torsionι G n) ≫ μ[G.X] =
      (fst _ _ ≫ torsionι G m) * (snd _ _ ≫ torsionι G n) := by
  rw [Hom.mul_def, lift_fst_comp_snd_comp]

/-- The two projections invert addition `G[m] ×_S G[n] ⟶ G` on the right. -/
private theorem tensorHom_torsionι_comp_mul_comp_lift :
    ((torsionι G m ⊗ₘ torsionι G n) ≫ μ[G.X]) ≫ lift (torsionFst hab hG) (torsionSnd hab hG) =
      𝟙 _ := by
  rw [tensorHom_torsionι_comp_mul]
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_ <;>
    simp [MonObj.mul_comp, torsionι_torsionFst, torsionι_torsionSnd, torsionι_torsionFst',
      torsionι_torsionSnd']

/-- The two projections invert addition `G[m] ×_S G[n] ⟶ G` on the left. -/
private theorem lift_comp_tensorHom_torsionι_comp_mul :
    lift (torsionFst hab hG) (torsionSnd hab hG) ≫ (torsionι G m ⊗ₘ torsionι G n) ≫ μ[G.X] =
      𝟙 _ := by
  rw [lift_map_assoc, torsionFst_torsionι, torsionSnd_torsionι, ← Hom.mul_def, ← zpow_add,
    add_comm, hab, zpow_one]

variable {hab hG}

/-- **A commutative group scheme killed by `m * n`, with `m` and `n` coprime, is the product of its
`m`-torsion and its `n`-torsion.** Addition `G[m] ×_S G[n] ⟶ G` is an isomorphism. -/
theorem isIso_tensorHom_torsionι_comp_mul (h : IsCoprime m n) (hG : 𝟙 G.X ^ (m * n) = 1) :
    IsIso ((torsionι G m ⊗ₘ torsionι G n) ≫ μ[G.X]) := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨lift (torsionFst hab hG) (torsionSnd hab hG), tensorHom_torsionι_comp_mul_comp_lift hab hG,
    lift_comp_tensorHom_torsionι_comp_mul hab hG⟩

/-- **The coprime splitting of a commutative group scheme.** If `G` is killed by `m * n`, with `m`
and `n` coprime, then addition is an isomorphism `G[m] ×_S G[n] ≅ G` of group schemes over `S`. -/
noncomputable def torsionTensorIso (h : IsCoprime m n) (hG : 𝟙 G.X ^ (m * n) = 1) :
    torsion G m ⊗ torsion G n ≅ (CommGrp.forget₂Grp (Over S)).obj G :=
  have := isIso_tensorHom_torsionι_comp_mul h hG
  Grp.mkIso' (asIso ((torsionι G m ⊗ₘ torsionι G n) ≫ μ[G.X]))

/-- The isomorphism `G[m] ×_S G[n] ≅ G` is addition. -/
@[simp]
theorem torsionTensorIso_hom_hom_hom (h : IsCoprime m n) (hG : 𝟙 G.X ^ (m * n) = 1) :
    (torsionTensorIso h hG).hom.hom.hom = (torsionι G m ⊗ₘ torsionι G n) ≫ μ[G.X] :=
  (rfl)

/-- The inverse of `G[m] ×_S G[n] ≅ G` is given by the two projections of `torsionBicone`. -/
private theorem torsionTensorIso_inv_hom_hom (hab : a * m + b * n = 1)
    (hG : 𝟙 G.X ^ (m * n) = 1) :
    (torsionTensorIso ⟨a, b, hab⟩ hG).inv.hom.hom = lift (torsionFst hab hG) (torsionSnd hab hG) :=
  Iso.inv_ext (f := (Grp.forget (Over S)).mapIso (torsionTensorIso ⟨a, b, hab⟩ hG))
    (tensorHom_torsionι_comp_mul_comp_lift hab hG)

/-- If `a * m + b * n = 1`, the projection of `G` to `G[m]` under `G ≅ G[m] ×_S G[n]` is
multiplication by `b * n`. -/
@[reassoc]
theorem torsionTensorIso_inv_hom_hom_fst_torsionι (hab : a * m + b * n = 1)
    (hG : 𝟙 G.X ^ (m * n) = 1) :
    (torsionTensorIso ⟨a, b, hab⟩ hG).inv.hom.hom ≫ fst _ _ ≫ torsionι G m = 𝟙 G.X ^ (b * n) := by
  rw [torsionTensorIso_inv_hom_hom hab]
  exact (lift_fst_assoc _ _ _).trans (torsionFst_torsionι hab hG)

/-- If `a * m + b * n = 1`, the projection of `G` to `G[n]` under `G ≅ G[m] ×_S G[n]` is
multiplication by `a * m`. -/
@[reassoc]
theorem torsionTensorIso_inv_hom_hom_snd_torsionι (hab : a * m + b * n = 1)
    (hG : 𝟙 G.X ^ (m * n) = 1) :
    (torsionTensorIso ⟨a, b, hab⟩ hG).inv.hom.hom ≫ snd _ _ ≫ torsionι G n = 𝟙 G.X ^ (a * m) := by
  rw [torsionTensorIso_inv_hom_hom hab]
  exact (lift_snd_assoc _ _ _).trans (torsionSnd_torsionι hab hG)

end TauCeti.GroupScheme

namespace TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme

universe u

/-- **A finite locally free commutative group scheme of rank `m * n`, with `m` and `n` coprime, is
the product of its `m`-torsion and its `n`-torsion.** Let `G` be a finite locally free commutative
group scheme over `S` whose rank is `m * n` at every point of `S`. Then addition
`G[m] ×_S G[n] ⟶ G` is an isomorphism. -/
theorem isIso_tensorHom_torsionι_comp_mul {S : Scheme.{u}} (G : FiniteFlatCommGroupScheme S)
    {m n : ℕ} (h : m.Coprime n) (hG : ∀ s, G.structureMap.finrank s = m * n) :
    IsIso ((GroupScheme.torsionι { X := G.toOver } m ⊗ₘ GroupScheme.torsionι { X := G.toOver } n) ≫
      μ[G.toOver]) :=
  GroupScheme.isIso_tensorHom_torsionι_comp_mul (Nat.isCoprime_iff_coprime.2 h) <| by
    rw [← Nat.cast_mul, zpow_natCast]
    exact G.pow_eq_one_of_finrank hG _

end TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme
