#![no_std]

mod affine;
pub mod local_lcs;
mod permutation;

use core::str::FromStr;

pub use affine::build_affine_permutation;
pub use affine::AffineIndex;
pub use affine::AffinePermutation;
pub use permutation::Permutation;

#[allow(dead_code)]
pub(crate) trait TikzDrawable {
    fn draw(&self, top: f32, bot: f32, color: &str) -> String;
}

extern crate alloc;

use alloc::format;
use alloc::string::String;

#[allow(dead_code)]
pub(crate) struct TikzPicture {
    code: String,
}

#[allow(dead_code)]
impl TikzPicture {
    pub fn new() -> Self {
        Self {
            code: String::from_str("\\begin{tikzpicture}[y=-1cm]\n").unwrap(),
        }
    }

    pub fn draw(&mut self, element: &impl TikzDrawable, top: f32, bot: f32, color: &str) {
        self.code +=
            &format!("\t\\draw[line cap=rect] (0,{top}) -- (\\linewidth-\\pgflinewidth,{top});");
        self.code +=
            &format!("\t\\draw[line cap=rect] (0,{bot}) -- (\\linewidth-\\pgflinewidth,{bot});");
        self.code += element.draw(top, bot, color).as_str();
        self.code += "\n";
    }

    pub fn to_string(self) -> String {
        self.code + "\\end{tikzpicture}\n\\vfill\n"
    }
}
