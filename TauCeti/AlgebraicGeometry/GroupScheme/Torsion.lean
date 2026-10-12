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
# Torsion of commutative group schemes and the coprime splitting

Let `G` be a commutative group scheme over a scheme `S`, that is, a commutative group object of
`Over S`, and let `n` be an integer. The `n`-torsion `G[n]` is the scheme-theoretic kernel of
multiplication by `n`, the integer `n` of the endomorphism ring `End_S(G)`. Its points with values
in any `Z` over `S` are the points of `G` killed by `n`.

If `G` is killed by `m * n`, with `m` and `n` coprime, then addition `G[m] ×_S G[n] ⟶ G` is an
isomorphism of group schemes over `S`. If `a * m + b * n = 1`, the projection of `G` to `G[m]` is
multiplication by `b * n`, and the projection to `G[n]` is multiplication by `a * m`. By Deligne's
theorem this applies to every finite locally free commutative group scheme over `S` of constant rank
`m * n`. Katz and Mazur use this splitting to reduce statements about level structures, such as the
generators of a finite locally free group scheme, to the prime-power case.

The argument is the splitting of an object of a preadditive category killed by a product of coprime
integers (`CategoryTheory.Limits.BinaryBicone.isBilimitOfCoprimeKernelForks`), applied in the
preadditive category `CommGrp (Over S)`.

## Main definitions

* `TauCeti.GroupScheme.torsion G n`: the `n`-torsion `G[n]`, a group object of `Over S`.
* `TauCeti.GroupScheme.torsionι G n`: its inclusion `G[n] ⟶ G`.
* `TauCeti.GroupScheme.torsionLift`: the point of `G[n]` given by a point of `G` killed by `n`.
* `TauCeti.GroupScheme.torsionTensorIso`: for `G` killed by `m * n` with `m` and `n` coprime, the
  isomorphism `G[m] ×_S G[n] ≅ G` of group schemes given by addition.

## Main results

* `TauCeti.GroupScheme.exists_comp_torsionι_iff`: the points of `G[n]` are the points of `G`
  killed by `n`.
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
  Studies 108, Princeton University Press, 1985, 1.10.14–1.10.15.
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry

namespace TauCeti.GroupScheme

universe u

variable {S : Scheme.{u}} (G : CommGrp (Over S))

/-! ### The `n`-torsion of a commutative group scheme -/

/-- **The `n`-torsion `G[n]` of a commutative group scheme** `G` over `S`: the scheme-theoretic
kernel of multiplication by `n`, the integer `n` of the endomorphism ring of `G`, as a group object
of `Over S`. -/
noncomputable def torsion (n : ℤ) : Grp (Over S) :=
  kernel ((CommGrp.forget₂Grp (Over S)).map (n : End G))

/-- The inclusion `G[n] ⟶ G` of the `n`-torsion of `G`, a morphism of `Over S`. -/
noncomputable def torsionι (n : ℤ) : (torsion G n).X ⟶ G.X :=
  (kernel.ι ((CommGrp.forget₂Grp (Over S)).map (n : End G))).hom.hom

/-- The inclusion of the `n`-torsion is a homomorphism of group schemes over `S`. -/
instance isMonHom_torsionι (n : ℤ) : IsMonHom (torsionι G n) :=
  (kernel.ι ((CommGrp.forget₂Grp (Over S)).map (n : End G))).hom.isMonHom_hom

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
  have h := kernel_ι_comp_hom ((CommGrp.forget₂Grp (Over S)).map (n : End G))
  rw [CommGrp.forget₂Grp_map_hom, CommGrp.intCast_hom_hom_hom] at h
  exact h

/-- The inclusion of the `n`-torsion, as a point of `G` with values in `G[n]`, is killed by `n`. -/
@[simp]
theorem torsionι_zpow (n : ℤ) : torsionι G n ^ n = 1 := by
  rw [← torsionι_comp_zpow G n, GrpObj.comp_zpow, Category.comp_id]

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

variable (G)

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
