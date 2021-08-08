import pygame
import sys
BLACK = (0, 0, 0)
WHITE = (255, 255, 255)
colors = [u'#1f77b4', u'#ff7f0e', u'#2ca02c', u'#d62728', u'#9467bd', u'#8c564b', u'#e377c2', u'#7f7f7f', u'#bcbd22', u'#17becf']
HEIGHT = 8
WIDTH = 8
N = 4
BLOCKS = [(3,3,5,0),(3,5,5,3),(5,3,0,5),(5,5,0,0)]
WINDOW_WIDTH = 20*WIDTH
WINDOW_HEIGHT = 20*HEIGHT

def main():
    global SCREEN, CLOCK
    pygame.init()
    SCREEN = pygame.display.set_mode((WINDOW_WIDTH, WINDOW_HEIGHT))
    CLOCK = pygame.time.Clock()
    SCREEN.fill(WHITE)

    while True:
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit()
                sys.exit()
        
        for i in range(len(BLOCKS)):
            block = BLOCKS[i]
            rect = pygame.Rect(block[2]*20, WINDOW_HEIGHT-block[3]*20-block[1]*20, block[0]*20, block[1]*20)
            pygame.draw.rect(SCREEN, colors[i], rect, 0)
        
        drawGrid()

        pygame.display.update()

        pygame.image.save(SCREEN, "out-1.png")
        sys.exit()


def drawGrid():
    blockSize = 20 #Set the size of the grid block
    for x in range(0, WINDOW_WIDTH, blockSize):
        for y in range(0, WINDOW_HEIGHT, blockSize):
            rect = pygame.Rect(x, y, blockSize, blockSize)
            pygame.draw.rect(SCREEN, BLACK, rect, 1)

main()